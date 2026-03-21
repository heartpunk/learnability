# Plan: Domain-Specific Extraction Pipeline

## Architecture

```
CFG blocks → stabilization → GenericExtractedLTS (persisted to disk as JSON)
                                    ↓
                          DomainExtractor typeclass
                         /         |          \
                    Grammar    OpSem/Rewrite   StateMachine
                   (parsers)   (interpreters)  (term emus)
```

The LTS is the interface boundary. Everything above it is proved (bisimulation). Everything below it is the extraction layer — currently unverified, target for incremental verification.

Key principle: **LTS on disk, extractors read it.** The stabilization doesn't re-run when iterating on extractors. The LTS JSON has states, transitions with symbolic labels and effects. Extractors are pure functions from LTS → domain artifact.

All predicate labels should be in SMT-LIB fragments for portability. All simplifiable subexpressions should be simplified to constants where possible.

## Phase 0: Shared Infrastructure

### Label Simplification
Apply reg+const LAS to guard PCs in the LTS, not just the sub. Currently guards contain `load8(store64(store64(mem, rbp-0x2d0, ...), rbp-0xb0c, ...), ptr+8)==0x13`. After LAS, this becomes `load8(mem, ptr+8)==0x13`.

Where: in `constructLTS` or as a post-processing pass on `GenericExtractedLTS`. Apply `simplifyLoadStorePC` (or the region-aware variant) to each transition's label comparisons.

### SMT-LIB Label Serialization
Each transition label's comparison expressions should be serializable as SMT-LIB assertions. Already have `SymExpr.toSMTLib` and `SymPC.toSMTLib`. Add to the LTS JSON output alongside the s-expression format.

### Extractor Typeclass (sketch)
```lean
class DomainExtractor (Domain : Type) where
  /-- Decode a transition label into a domain-specific token -/
  decodeLabel : DispatchKey → Option Domain.Token
  /-- Group transitions by domain-relevant equivalence -/
  groupTransitions : GenericExtractedLTS → Array (Domain.Group)
  /-- Extract domain artifact from grouped LTS -/
  extract : Array Domain.Group → Domain.Artifact
```

Don't over-design this upfront. Let it emerge from the concrete instances.

## Phase 1: Grammar Extraction Fix

### Goal
tinyc 15/20 → 20/20. Fix existing `DispatchLoopGrammar.lean`.

### Steps
1. **Apply label simplification to LTS guard PCs** — the `extractLTS` in `DispatchLoopGrammar.lean` already builds an LTS from body branches. Add `simplifyLoadStorePCOpt addrClassify` to the guard PCs before decoding to CharClass.

2. **Fix CharClass decoding** — audit `decodeCharClass` for cases that produce `.any` when they should produce specific ranges. The simplified guards should make this mostly work.

3. **Fix token discrimination** — `ltsExtractProds` uses accumulated guard heuristics to decide terminal vs nonterminal. Compare against the known-good stalagmite output to identify what's wrong.

4. **Test** — tinyc should hit 20/20 or close. cjson/json/parson should improve.

### Verification
Read tinyc LTS from disk. Run extraction. Compare against golden grammar. No stabilization re-run needed.

### Provability Target
State: the extracted grammar G is a simulation of the LTS L. `G.Simulates L` via the existing `LTS.Simulates` infrastructure. The witness relation maps grammar derivation states to LTS states. This is a stretch goal — get the extraction correct first, prove it later.

## Phase 2: OpSem Extraction

### Goal
Extract K-framework-style rewrite rules from Lua and MJS interpreter LTSes.

### Steps
1. **Read LTS from disk** — parse the JSON, reconstruct `GenericExtractedLTS` (or work directly from JSON in a Python/Lean script).

2. **Simplify labels** — same as Phase 0. Get `load8(mem, bytecode_ptr)==0x13` instead of nested store chains.

3. **Decode opcode values** — extract the constant from each simplified guard comparison. Map to opcode name if the binary's symbol/data sections are available (e.g., Lua's `luaP_opnames` array).

4. **Group by opcode** — all transitions with label `==0x13` go in one group. Already have `extractDispatchTable` which does this.

5. **Anti-unify effects within each group** — for each opcode group, collect the `effects` (symbolic substitutions) from all transitions. Anti-unify using existing `AntiUnify.lean` to extract the opcode's semantic template. Template holes = instruction operands (register indices, immediate values).

6. **Emit rewrite rules** — format each opcode's template as:
   ```
   rule OPCODE(hole1, hole2, ...) :
     reg[X] := template_expr(hole1, hole2, ...)
     mem := template_mem(hole1, hole2, ...)
   ```

### Test Subjects
- Lua: 688 opcode labels → ~50 unique opcodes × multiple operand patterns
- MJS exec_expr: 218 labels → AST node type dispatch
- MJS mjs_execute: 286 labels → bytecode dispatch

### Provability Target
Anti-unification soundness is already proved. The extracted template, when instantiated with any valid operand values, produces a valid LTS transition. This is `antiUnifyExpr_left` / `antiUnifyExpr_right` applied to the effects.

## Phase 3: State Machine Extraction

### Goal
Extract state machine tables from libtsm and st terminal emulators.

### Steps
1. **Read LTS from disk.**

2. **Identify mode states** — LTS states cluster by "escape processing phase." Normal mode → ESC received → CSI/OSC/DCS → parameter accumulation → command dispatch. Group states by the escape sequence prefix that reaches them.

3. **Decode input symbols** — guard PCs are character comparisons (`==0x1b` for ESC, `==0x5b` for `[`, `==0x41` for cursor up). Decode to human-readable input tokens.

4. **Extract transitions** — for each (state, input) pair, the LTS gives the target state and the effects (screen mutation). Format as state machine table.

5. **Emit** — table format: `(mode, input) → (next_mode, actions)` where actions are the effects on cursor position, attributes, screen buffer.

### Test Subjects
- libtsm do_csi: 267 states, 57 distinct labels — CSI command dispatch
- libtsm do_action: 89 states — action type dispatch
- st tputc: 139 states, 291 labels — full character processing

### Provability Target
The state machine is a quotient of the LTS by mode equivalence. If two LTS states respond identically to all input sequences, they're in the same mode. This is a bisimulation quotient — refinement of the one we already proved.

## Phase 4: QuickJS Investigation

### Goal
Understand why 1584 transitions collapse to 1 equivalence class.

### Steps
1. **Inspect the 268 closure guards** — are they opcode-discriminating or just shared type checks?
2. **Check if rip guards are the real discriminator** — for jump table dispatch, the rip target encodes the opcode. Currently filtered as "structural routing."
3. **Try including rip guards in closure** — see if equivalence classes separate.
4. **Check CFG extraction** — does `extract_cfg.py` resolve the jump table? If not, all opcode paths merge at the CFG level before symbolic execution.

## Execution Plan

Sequential, one phase at a time. Each phase:
1. Read LTS from disk (no re-stabilization)
2. Implement extractor
3. Test on target subjects
4. Commit
5. Move to next phase

Alternate between grammar fixes and opsem to stay balanced. Grammar is closest to done; opsem is highest novelty. State machine is validation that the pattern generalizes.

Estimated: Phase 0 (1 session), Phase 1 (1 session), Phase 2 (2 sessions), Phase 3 (1 session), Phase 4 (investigation, 1 session).
