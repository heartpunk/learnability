# Principled Grammar Detection Design (2026-03-19)

## Problem

Gated detectParser entirely, losing terminal extraction. Need to replace
heuristic detection (IsTokenConfig, consumer analysis) with principled
detection that works for all subjects.

## Design: Three-phase classification

### Phase 1: Lexer identification (keep findProducers)

`findProducers` identifies the function that writes the most distinct constant
values to a consistent location. This IS the lexer. Works reliably across
subjects. Not a heuristic — direct observation of function behavior.

### Phase 2: Call graph classification

Given lexer L:
- **Grammar NT**: directly calls L (edge to L in call graph)
- **Wrapper**: transitively reaches L but no direct edge
- **Helper**: never reaches L transitively

One call graph lookup per function. Zero heuristics. Uses WTO structure
naturally — wrappers are linear vertices above the recursive component.

### Phase 3: Terminal extraction + wrapper inlining

- Token name table: from lexer summary branches (output value → input guard)
- Terminal extraction: `extractNTGrammar` already does this when given lexer info
- Wrapper inlining: replace wrapper refs in productions with their call targets

## Connection to formal framework

The closed projection (computed during stabilization) identifies which registers
carry meaningful state. If a function's projection includes the token register
(rax after lexer call), it's input-dependent. This instantiates the co-refinement
criterion: "dimension d matters because changing d causes behavioral divergence."

## Implementation (~100-150 lines in DispatchLoopPipeline.lean)

1. Call findProducers to identify lexer (reuse existing)
2. Classify by direct-call-to-lexer (~20 lines)
3. Build token name table from lexer summary (reuse existing)
4. Filter to grammar NTs, pass lexer info to printLTSGrammar (~30 lines)
5. Wrapper inlining in production extraction (~50 lines)

## Expected results

- Terminal extraction restored (was 18/20 for tinyc with --functions)
- Wrapper filtering removes noise (main, parse_expr, etc.)
- Structural comparison gets real terminal content
- Dramatic improvement across all subjects
