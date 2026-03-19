# Principled LTS Extraction + Domain Interpretation Design (2026-03-19)

## Architecture: Generic Core + Domain Layers

### Generic Core (domain-independent)

The core extracts structural information from converged summaries without
knowing what domain (grammar, state machine, opsem) the subject belongs to.

**Per-function structural metadata:**
- `branchingDimensions`: which projected registers/memory slots the function
  branches on (from closedRegs + PC guard analysis)
- `branchingValues`: what values on those dimensions cause different behavior
  (from PC guard constants)
- `callPattern`: which functions are called under which guards
  (from body branch rip targets + PC guards)
- `structuralRole`: from WTO position + body analysis
  - `component_member`: in a recursive SCC — participates in iteration
  - `component_head`: SCC head — controls iteration
  - `linear_vertex`: not in any SCC — sequential
  - `leaf`: no calls to other analyzed functions
- `amplification`: ratio of summary branches to body branches
  (high = lots of iteration/composition, low = simple delegation)

This metadata is computed once after wtoFixpoint and is available to all
interpretation layers.

### Grammar Interpretation Layer

Maps structural metadata to grammar concepts:

1. **Lexer identification**: find the leaf function whose branchingValues
   partition the input byte space most finely. This is `findProducers` —
   a grammar-specific heuristic, NOT in the core.

2. **NT classification**: functions that directly call the lexer
   (grammar-specific — uses call graph + lexer identity).

3. **Terminal extraction**: branchingValues from post-lexer-call guards
   mapped to character classes (grammar-specific).

4. **Wrapper detection**: functions that reach the lexer transitively
   but never directly — inline into callers' productions.

5. **Production extraction**: group summary branches by call pattern,
   emit sequence of terminals + NTs per group.

### State Machine Interpretation Layer

Maps structural metadata to automaton concepts:

1. **State identification**: each function is a state (or each block within
   a function). BranchingValues on the input byte = transition labels.

2. **Transition extraction**: for each branchingValue, which function/block
   is the target? That's a transition.

3. **Action identification**: side effects (memory writes, register changes)
   at each transition = the action on that transition.

4. **No lexer needed**: terminals are raw input bytes, read from the
   branchingDimensions directly.

### Operational Semantics Interpretation Layer

Maps structural metadata to reduction rules:

1. **Opcode identification**: branchingValues on the dispatch dimension
   = opcode constants.

2. **Rule extraction**: for each opcode, the substitution delta = the
   reduction rule's effect on the abstract machine state.

3. **State component naming**: the branchingDimensions + projected registers
   correspond to the abstract machine's cells (PC, stack, env, etc.)
   Named post-hoc or by heuristic.

## Core Implementation

### New: `extractStructuralMetadata`

```
def extractStructuralMetadata
    (functions : Array FunctionSpec)
    (summaries : HashMap UInt64 (Array Branch))
    (wto : Array WTOElem)
    (callGraph : Array (UInt64 × UInt64))
    : HashMap UInt64 FunctionMetadata
```

For each function:
1. Read its closedRegs (from stabilization — already computed)
2. Analyze body branch PCs: which registers appear in guards?
   What constant values are compared?
3. Analyze body branch call targets: which functions called under
   which guards?
4. Classify structural role from WTO position
5. Compute amplification ratio

### Domain layers call this, then interpret

```
-- Grammar layer
def grammarInterpretation (meta : HashMap UInt64 FunctionMetadata) : GrammarResult
-- State machine layer
def stateMachineInterpretation (meta : HashMap UInt64 FunctionMetadata) : AutomatonResult
-- Opsem layer
def opsemInterpretation (meta : HashMap UInt64 FunctionMetadata) : ReductionRules
```

## What stays from current code

- `wtoFixpoint` — unchanged
- `computeFunctionStabilization` — unchanged (already computes closedRegs)
- `buildCallGraph` — unchanged
- `extractNTGrammar` — becomes part of grammar interpretation layer
- `printLTSGrammar` — becomes part of grammar interpretation layer
- `findProducers` — becomes grammar-specific heuristic
- `structuralGoldenCompareV2` — stays in grammar layer

## What changes

- `runPipelineWTO` calls `extractStructuralMetadata` after fixpoint
- Passes metadata to whichever interpretation layer is requested
- `--grammar` (default for parser subjects), `--state-machine`,
  `--opsem` flags select interpretation
- Grammar layer uses findProducers + call-graph classification
  (the "not general" stuff from before — but correctly scoped as
  domain-specific, not core)

## Connection to formal framework

The `branchingDimensions` field IS the co-refinement fixpoint projection
(closedRegs). The `branchingValues` are the concrete witnesses that caused
dimension refinement to include those dimensions. The formal guarantee:
at the fixpoint, these dimensions are sufficient to distinguish all
behaviorally different states.

Domain layers interpret what those dimensions MEAN (tokens, bytes, opcodes)
but the core guarantee holds regardless of interpretation.
