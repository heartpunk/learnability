# Parser Detection Research Notes — 2026-03-13

## Key Finding: Stalactite Already Has Formal Predicates

`~/code/stalactite/lean/RDParserAnalysis.lean` has proved predicates:

- **IsTokenConfig(G, v, lex)**: v = token variable, lex = unique writer, ≥2 readers call lex
- **IsNT(G, v, lex, f)**: f reachable from entry, reads v, transitively calls lex, f ≠ lex
- **IsTokenConfigExt**: writer SET generalization (lexer modes, virtual injection)
- **IsNTExt**: nonterminal with writer set
- **T1-T4 proved**: disjointness, exhaustive classification, monotonicity, NT closure

These are the RIGHT predicates. Our ParserDetection should instantiate them, not reinvent.

## My Original Heuristics Were Wrong

- "isLeaf" — WRONG. Lexers can call helpers. Right criterion: unique writer of token var.
- "readsInput" — FRAGILE. Right criterion: data-flow on token variable.
- "returns integer in rax" — x86-64 specific. Right: writes to the token variable.

## Stalagmite Test Set (9 subjects)

| Subject | Style | Parser? | Notes |
|---------|-------|---------|-------|
| tinyc | RDP | Yes | Mutual recursion, 7 NTs |
| json | RDP + loops | Yes | Whitespace, escapes |
| cJSON | RDP | Yes | JSON variant |
| parson | RDP | Yes | JSON variant |
| lisp | RDP + explicit lex | Yes | S-expressions |
| calc | RDP + OPP | Yes (two versions!) | Operator precedence variant |
| simplearithmeticparser | RDP (C++) | Yes | C++ class-based |
| cgi_decode | State machine | **Coupled** | Regular lang, no recursion |
| mjs | VM | **Coupled** | Not a parser — JS VM semantics |

**SOPHIE'S CORRECTION:** cgi_decode and mjs have parsers COUPLED to non-parsers.
The analysis above is not quite right — need to re-examine what "coupled" means here.
These may have parser components entangled with non-parser functionality, which is
exactly the case where manual annotation (parser slicing) would be needed.

## Stalactite Parser Typology

### World 1: Imperative-LL-Static (21 parsers)
- Token-based: global variable holds current token
- Core: reads token → call lexer → consume
- Examples: Clang, V8, QuickJS, Lua, micropython, ANTLR4, Swift, GCC C++, Wren

### World 2: Combinator-Backtracking-Extensible (4 parsers)
- Character-level, no global token state
- Monadic/continuation abstraction
- Examples: attoparsec, megaparsec, pappy, xml_conduit
- OUT OF SCOPE for current work

### Extensions needed for full World 1 coverage:
- **+Mode** (11 parsers): per-mode writer sets for lexer modes
- **+Writers** (4): multi-writer tokenizers
- **+CalleeSet** (8): Pratt/dispatch patterns (DetectsBlockSet)
- **+CleanTrace** (9): recovery event filtering

## Revised ParserDetection Design

### Core change: instantiate stalactite's ParserGraph

Build `ParserGraph UInt64 UInt64` from converged branches where:
- Functions = entry addresses
- calls(f, g) = ∃ branch in f with rip target = g's entry
- reads(f, v) = ∃ branch in f with guard comparing value at address v
- writes(f, v) = ∃ branch in f that stores to address v

Then check IsTokenConfig on this graph. If it holds, we have constructive evidence.

### Token variable identification at binary level
The token variable is a MEMORY ADDRESS (not a register). In Tiny C, `sym` lives at
a fixed address. At the VEX level:
- next_sym STORES to that address (writes token type)
- NT functions LOAD from that address and branch on the value

This is different from what I proposed (rax-based). The rax value at function return
is the C calling convention's way of returning, but the actual token variable is in memory.

However: for the stalagmite subjects (compiled C), the calling convention means the
token value flows through rax at call boundaries. So rax-based detection works for
THIS architecture, but the principled approach uses memory data flow.

### Two-phase approach
1. **Now:** rax-based detection (works for compiled C on x86-64, covers stalagmite)
2. **Future:** memory data-flow detection (general, aligns with IsTokenConfig)

### What "conservative" means for stalagmite
- tinyc, json, cJSON, parson, lisp, calc/rdp, simplearithmeticparser: detect YES
- calc/opp: detect YES (still has tokenizer, just different NT structure)
- cgi_decode: needs investigation — sophie says coupled, not just "not a parser"
- mjs: needs investigation — sophie says coupled

## Open Questions (for sophie)

1. What does "coupled" mean for cgi_decode and mjs? Parser entangled with non-parser?
2. Should we handle the coupled case now, or is that the manual annotation path?
3. For stalagmite validation: do we need golden grammars for all 9, or start with the
   ones that are clearly RDP?

## Connection to Plan

The ParserDetection.lean plan needs revision to:
1. Use IsTokenConfig-aligned criteria instead of isLeaf/readsInput
2. Build a ParserGraph from branches (instantiate stalactite's abstract framework)
3. Handle the coupled case (at least detect + warn, defer to manual annotation)
4. Keep rax-based token type detection as architecture-specific fast path
5. Note: the stalactite predicates are ALREADY PROVED — we should import or mirror them

## Files Referenced
- `~/code/stalactite/lean/RDParserAnalysis.lean` — formal predicates (T1-T4)
- `~/code/stalagmite/subjects/` — 9 test subjects
- `~/code/stalagmite/data/golden_grammars/` — golden grammars (JSON)
- `~/code/familiar/notes/rd-parser-morphfield.md` — complete typology
- `~/code/familiar/notes/rd-parser-fca-schema.md` — FCA population schema
