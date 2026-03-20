# Generic LTS Core + Domain Interpretation Layers (2026-03-19)

## Target Specification Classes

1. **Parsers/Grammars** — dispatch on token value → productions
2. **State machines** — dispatch on (state, input byte) → transitions
3. **Bytecode interpreters** — dispatch on opcode → reduction rules
4. **Type systems** — dispatch on AST node tag (+ substructure) → typing rules
5. **Effect systems** — dispatch on effect label → handler clauses
6. **Macro expanders** — dispatch on syntax form tag (+ argument shape) → expansion rules
7. **Compilers** — dispatch on AST node tag → compilation rules

## Universal Structure

Every class: dispatches on constants in PC guards, branches based on those
values, produces effects in the substitution. The dispatch values are the
"labels" of the extracted LTS. The effects are the "transitions."

## Key Insight: Dispatch Depth Varies

- **Single-level** (parsers, interpreters, simple state machines): one
  comparison per branch. `eq(rax, TOKEN_IF)`.
- **Multi-level** (type systems, macro expanders, pattern matching): nested
  comparisons. `eq(node_tag, APP) ∧ eq(arg_type_tag, ARROW)`.

At the branch level, multi-level dispatch is conjunctions in the PC guard.
The core doesn't distinguish — it extracts ALL comparisons as a tuple.

## Core Data Structures

```lean
/-- A dispatch key: the full tuple of equality comparisons from a branch's PC.
    For a parser branch: [(rax, 5)] (token value).
    For a type system: [(node_tag, 3), (subtype_tag, 7)] (AST + type structure).
    For a state machine: [(state_var, 2), (input_byte, 0x1B)] (state + input). -/
structure DispatchKey where
  comparisons : Array (SymExpr × UInt64)

/-- A group of branches sharing the same dispatch key.
    Each group corresponds to one rule/transition/production. -/
structure BranchGroup where
  key : DispatchKey
  branches : Array Branch
  callTargets : Array UInt64    -- functions called within this group
  isRecursive : Bool            -- does the group call back into the same function?

/-- Per-function dispatch table: the complete structure of a function's behavior. -/
structure FunctionDispatchTable where
  funcAddr : UInt64
  funcName : String
  groups : Array BranchGroup
  dimensions : Array SymExpr    -- which expressions are dispatched on (auto-discovered)
  projectedRegs : Array Reg     -- from co-refinement fixpoint (closedRegs)
  bodyBranchCount : Nat
  summaryBranchCount : Nat
```

## Core Algorithm: `extractDispatchTable`

For each function's converged summary branches:

1. **Extract comparisons**: For each branch, walk the PC and collect all
   `eq(expr, const)` conjuncts. The `expr` is a dispatch dimension, the
   `const` is the dispatch value.

2. **Discover dimensions**: The set of all distinct `expr` values across
   branches. These are the function's dispatch dimensions. For a parser:
   `[rax]`. For a state machine: `[mem[state_ptr], rdi]`. For a type
   checker: `[mem[node_tag_offset], mem[subnode_tag_offset]]`.

3. **Group by key**: Branches with identical comparison tuples form a group.
   Each group is one "rule" in whatever domain we're extracting.

4. **Extract call targets**: Within each group, which functions are called
   (from rip targets in the substitution).

5. **Detect recursion**: Does any group contain a call back to the same
   function?

This is ~50-80 lines of code. Domain-independent. Works for all seven classes.

## Domain Interpretation Layers

Each layer reads the dispatch table and maps it to domain vocabulary.

### Grammar Layer

```
lexer = findProducers(functions, summaries)  -- grammar-specific heuristic
for func in functions:
  if func directly calls lexer:  -- grammar NT
    for group in func.dispatchTable.groups:
      terminal = tokenNameTable[group.key]  -- map dispatch value to token name
      nts = group.callTargets.filter(isGrammarNT)
      emit production: func -> terminal nts...
  else if func transitively reaches lexer:  -- wrapper
    inline into callers
  else:  -- helper
    skip
```

### State Machine Layer

```
for func in functions:
  for group in func.dispatchTable.groups:
    state = group.key.comparisons.find(isStateVar)
    input = group.key.comparisons.find(isInputByte)
    effects = extractSubstitutionDelta(group.branches)
    emit transition: (state, input) → (newState, effects)
```

State variable identification: the dispatch dimension that appears in BOTH
the PC guard (current state check) AND the substitution (state update).
A dimension that's read and written is a state variable.

### Operational Semantics Layer

```
for func in functions:
  for group in func.dispatchTable.groups:
    opcode = group.key.comparisons[0].const  -- dispatch value = opcode
    effects = extractSubstitutionDelta(group.branches)
    emit rule: opcode → effects on (PC, stack, memory, ...)
```

State component identification via co-refinement projection: the projected
registers from stabilization tell us which state matters. The component
that increments uniformly = instruction pointer. The component that goes
up/down = stack pointer. Post-hoc naming, not heuristic detection.

### Type System Layer

```
for func in functions:  -- e.g., typecheck()
  for group in func.dispatchTable.groups:
    node_tag = group.key.comparisons[0].const
    substructure = group.key.comparisons[1:]  -- deeper dispatch
    effects = extractSubstitutionDelta(group.branches)  -- type output
    emit rule: node_tag (+ substructure) → type assignment
```

Multi-level dispatch key naturally captures nested pattern matching on
AST node types and substructure.

### Compiler Layer

Same as type system layer but effects = emitted code instead of types.
The `c` function in tinyc already demonstrated this — each dispatch group
maps an AST node type to a bytecode emission pattern.

### Effect System Layer

```
for func in functions:  -- e.g., handle()
  for group in func.dispatchTable.groups:
    effect_label = group.key.comparisons[0].const
    handler_body = extractSubstitutionDelta(group.branches)
    continuation = group.callTargets  -- how execution resumes
    emit clause: effect_label → handler_body, continuation
```

### Macro Expander Layer

```
for func in functions:  -- e.g., expand()
  for group in func.dispatchTable.groups:
    form_tag = group.key.comparisons[0].const
    arg_checks = group.key.comparisons[1:]  -- argument count/shape
    expansion = extractSubstitutionDelta(group.branches)  -- output syntax
    emit rule: form_tag (+ arg_checks) → expansion
```

## Connection to Formal Framework

The `dimensions` field in `FunctionDispatchTable` IS the co-refinement
fixpoint projection instantiated for the function. The formal guarantee:
at the fixpoint, these dimensions are sufficient to distinguish all
behaviorally different states. Domain layers interpret what those
dimensions MEAN but the soundness guarantee holds regardless.

`extractDispatchTable` is the concrete implementation of "read the
co-refinement fixpoint" — it takes the already-computed closedRegs
and the converged branches, and groups them by their dispatch structure.

## Implementation Plan

### Phase 1: Core (~80 lines, DispatchLoopPipeline.lean or new file)
- `extractComparisons : SymPC → Array (SymExpr × UInt64)`
- `extractDispatchTable : FunctionSpec → Array Branch → FunctionDispatchTable`
- Wire into `runPipelineWTO` after fixpoint, before domain layers

### Phase 2: Grammar Layer (~100 lines)
- Restore `findProducers` call (lexer identification)
- Classify by direct-call-to-lexer
- Build token name table
- Map dispatch groups to productions
- Wire into `printLTSGrammar`

### Phase 3: State Machine Layer (~80 lines)
- State variable identification (dimension read+written)
- Transition extraction from dispatch groups
- Output format TBD (graphviz? JSON?)

### Phase 4: Opsem Layer (~80 lines)
- Opcode identification from dispatch groups
- Substitution delta extraction
- K-style rule formatting (or simpler initial format)

## What This Replaces

- `detectParser` → grammar layer's findProducers + call-graph classification
- `IsTokenConfig` → unnecessary (dispatch table has the structure directly)
- Grammar-specific `printLTSGrammar` → grammar layer reading dispatch tables
- Nothing changes in wtoFixpoint or computeFunctionStabilization
