# Extraction Gaps Analysis & Roadmap

## Current State

The stabilization pipeline produces correct LTSes (proved via bisimulation, zero sorries). The LTS data is rich:

| Subject | Type | States | Transitions | Labels | Structure Quality |
|---------|------|--------|-------------|--------|-------------------|
| tinyc | RD parser | 16-77/fn | 31-59/fn | char dispatch | **Good** — 15/20 golden |
| mjs parser | RD parser | varies | varies | char dispatch | **Good** — precedence tower recovered |
| cjson | RD parser | varies | varies | char dispatch | **Good** — value/object/array |
| lua | bytecode interp | 1046 | 2317 | 688 opcode labels | **Rich LTS, no extraction** |
| mjs interp | AST interp | 271+399 | 1075+1371 | 218+286 AST tags | **Rich LTS, no extraction** |
| quickjs | bytecode interp | 1572 | 1584 | collapsed to 1 class | **LTS exists but grammar collapsed** |
| libtsm | terminal emu | 89-267/fn | 353-430/fn | CSI codes/actions | **Rich LTS, no extraction** |
| st | terminal emu | 139 | 1380 | 291 char/mode labels | **Rich LTS, no extraction** |

## Gap 1: Grammar Extraction Quality (Parser Subjects)

### Problem
tinyc gets 15/20 instead of 20/20. Missing: `term → id | int | paren_expr` (1/3), `sum → sum - term` (missing `-`), extra spurious productions.

### Root Cause
`ltsExtractProds` in `DispatchLoopGrammar.lean` does DFS through the LTS with ad-hoc decisions:
- Terminal vs nonterminal classification is based on "is this a call to the lexer function?"
- Recursion detection is based on back-edges in DFS, not on semantic loop structure
- Token discrimination uses accumulated guard heuristics that miss some cases

### Fix
1. **Simplify closure PC labels** — apply reg+const LAS to guard PCs (same optimization we did for subs). Currently guards contain `load8(store64(...), addr)` chains that should simplify to `load8(mem, addr)`.
2. **Improve CharClass decoding** — the `decodeCharClass` function maps guard PCs to character ranges. Some guards decode to `any` when they should decode to specific ranges.
3. **Connect to bisimulation** — the grammar extraction is unverified. The LTS→grammar step should produce a witness that the grammar accepts exactly the traces of the LTS. This is a simulation proof between the grammar's NFA and the extracted LTS.

### Provability
The LTS is proved correct (bisimulation). The grammar extraction COULD be proved correct by showing: every LTS trace corresponds to a grammar derivation (completeness) and every grammar derivation corresponds to an LTS trace (soundness). This is a simulation between the grammar-as-NFA and the LTS. The `LTS.Simulates` infrastructure exists.

## Gap 2: Interpreter/Opsem Extraction (Bytecode Subjects)

### Problem
Lua, MJS interpreter, QuickJS have rich LTSes with hundreds of opcode-guarded transitions, but the grammar extraction produces nothing because:
1. Grammar extraction equates functions with nonterminals — single-function interpreters get one NT
2. All opcode branches collapse to one semantic equivalence class (same PC signature)
3. No interpretation layer for "opcode → semantic rule"

### Root Cause
The extraction pipeline assumes parser structure: function = nonterminal, lexer call = terminal. Interpreters have different structure: one function, opcode dispatch = transition label, stack/register effects = semantic rule.

### Fix: Pluggable Interpretation Layer
The `GenericExtractedLTS` already has `effects : Option (SymSub Amd64Reg)` on each transition. For opsem extraction:

1. **Group by opcode** — dispatch groups already computed (`extractDispatchTable`). Each group = one opcode.
2. **Simplify labels** — apply LAS to guard PCs to get clean opcode expressions like `load8(mem, bytecode_ptr)==0x13`.
3. **Extract opcode values** — decode the constant from the simplified guard. Map to opcode name from binary's data section if available.
4. **Anti-unify effects** — for each opcode group, anti-unify the symbolic substitutions across instances. Template holes = instruction operands. Template structure = opcode semantics.
5. **Emit rewrite rules** — K-framework style: `<k> OPCODE args ~> . </k> <state> effects </state>`.

### Provability
The LTS is proved correct. The opcode grouping is a partition of transitions (verifiable). The anti-unification is proved sound (`antiUnifyExpr_left/right` exist). The gap: connecting the anti-unified template to a rewrite semantics. This requires showing that instantiating the template with any valid operands produces a valid LTS transition — which IS the anti-unification soundness property.

## Gap 3: State Machine Extraction (Terminal Emulators)

### Problem
libtsm and st have rich LTSes dispatching on escape codes, character values, and mode flags. Grammar extraction ignores them (produces empty/trivial).

### Root Cause
Same as interpreters: grammar extraction assumes parser structure. Terminal emulators are state machines — states are modes (normal, escape, CSI, etc.), transitions are character/code inputs, effects are screen/attribute mutations.

### Fix
1. **State identification** — LTS states already correspond to code addresses. Group by "escape processing mode" (normal → ESC seen → CSI → parameter accumulation → dispatch).
2. **Transition labeling** — decode character/code from guard PCs. The guards are already character-level (`load8 ... == 0x1b` for ESC, `== 0x5b` for `[`).
3. **Effect extraction** — the symbolic substitutions describe attribute mutations (cursor position, color, mode flags). These ARE the state machine's output actions.
4. **Emit state machine** — states × inputs → (next_state, output_actions).

### Provability
Same as opsem: LTS is proved, partitioning is verifiable, label decoding is a function from guard PCs to input symbols. The state machine is a quotient of the LTS by "mode equivalence" which is a refinement of the bisimulation quotient.

## Gap 4: QuickJS Collapse

### Problem
QuickJS has 1584 transitions but all collapse to 1 PC-signature equivalence class. The LTS exists but every branch has the same semantic signature — they all satisfy the same closure PCs.

### Root Cause
The closure has 268 data guards. Every composed branch satisfies the same 268 guards (or doesn't) in the same pattern. This suggests the guards are too coarse — they don't distinguish between opcodes. The opcode dispatch happens via a computed jump (indirect branch through a jump table), which the symbolic execution might not fully resolve.

### Fix
1. **Investigate the 268 closure guards** — are they actually opcode-discriminating or are they all data-type checks that every path shares?
2. **Jump table resolution** — if the opcode dispatch is via indirect jump, the CFG extraction (`extract_cfg.py`) needs to resolve the jump table targets. Currently it might merge all targets.
3. **Finer-grained closure** — the convergence uses "data-only" closure (filters out rip guards). For a jump-table dispatch, the rip guard IS the opcode discriminator. Including rip guards in the closure might separate the equivalence classes.

## Unified Architecture: The Generic LTS Layer

All three gaps (grammar, opsem, state machine) share the same pattern:
1. Start with the proved-correct LTS
2. Decode transition labels from symbolic expressions to domain-specific tokens
3. Group/quotient the LTS by domain-specific equivalence
4. Extract domain-specific artifact (grammar / rewrite rules / state machine)

This is exactly the "generic LTS + pluggable interpretation" design from the project memory. The `Core/LTS.lean` formal type, the `GenericExtractedLTS` computational type, and the `DispatchKey` label type are the infrastructure. What's missing is the interpretation plugins and the proofs connecting them to the LTS bisimulation.

## Priority Order

1. **Simplify closure PC labels** — unblocks all extraction (parser, interpreter, terminal). Pure engineering, uses existing reg+const LAS.
2. **Fix grammar extraction for parsers** — improve tinyc 15→20, fix token discrimination. Closest to provable.
3. **Opsem extraction via anti-unification** — Lua and MJS. High impact, uses existing anti-unification infrastructure.
4. **State machine extraction** — libtsm and st. Similar to opsem but simpler (no operand decoding).
5. **QuickJS collapse investigation** — needs jump table / indirect branch resolution.
6. **Proof connection** — wire extraction artifacts to LTS bisimulation via simulation proofs.
