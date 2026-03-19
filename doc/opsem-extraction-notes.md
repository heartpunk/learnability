# Operational Semantics Extraction — Analysis Notes (2026-03-18)

## Existing Data Assessment

### tinyc `run` — bytecode interpreter (BEST CANDIDATE)
- 158 converged branches from 57 body branches, K=2 convergence
- 11 opcodes: IFETCH, ISTORE, IPUSH, IPOP, IADD, ISUB, ILT, JMP, JZ, JNZ, default/halt
- LTS extraction shows 36 states, 56 transitions — the full dispatch automaton
- Grammar extraction (lossy) produced: `run -> run` (loop) + `run -> tokN` (9 halt cases)
- Substitutions contain stack/memory effects but are discarded by grammar extraction
- **The data for K-style rule extraction already exists in the converged summaries**

### tinyc `c` — tree-walking compiler
- 261 converged branches from 116 body branches, K=2
- Productions directly mirror AST node type dispatch: `c -> tok7 c c` (binary op), `c -> tok5` (leaf)
- Viable for compiler rule extraction — shows compilation patterns per AST node type

### lisp `run_lisp` — S-expression evaluator
- 37 converged branches, K=0 (flat dispatch, single pass)
- 29 body branches = switch on AST node type
- **Problem**: call graph is sparse — calls to `_plus_`, `print_scm` go through indirect dispatch
- Partial data: the dispatch structure is captured but callee summaries are disconnected

### lisp `_plus_` — arithmetic built-in
- 28 converged branches, K=2 (loop unrolling visible)
- No consumer relationship links it to `run_lisp` (orphaned)

### mjs `exec_expr` / `mjs_execute` — JS interpreter
- **BLOCKED**: PARSE ERROR on xmm1 (SSE register). JS numbers are IEEE 754 doubles.
- Zero mjs non-parser functions converged. VEX float/SSE gap blocks everything.

## What's Needed for Opsem Extraction

### Data already available (no new collection needed)
- Per-function converged summaries: `HashMap UInt64 (Array (Branch SymSub SymPC))`
- Each branch has both PC (dispatch guard) and Sub (register/memory effects)
- The substitution Sub maps every register to a symbolic expression + memory chain

### Extraction approach
1. **Opcode identification**: Extract dispatch guard from PC — which constant is being compared
2. **Effect extraction**: For each register/memory in Sub, compute delta from identity
3. **State component detection**: Identify bytecode PC (increments by 1-2 per handler),
   stack pointer (goes up/down), stack contents (relative to SP), globals (fixed base)
4. **Rule formatting**: Template into K Framework notation or similar

### Gap from our data to K rules
Our branch: `{pc: eq(load(.w32, mem, rbp-16), 5), sub: {mem -> store(...)}}`
K rule: `rule <k> IADD => . ...</k> <stack> V1 : V2 : S => (V1 +Int V2) : S </stack>`

The transformation requires:
- Mapping `rbp-16` → "bytecode PC variable"
- Mapping `rbp-24` → "stack pointer variable"
- Recognizing load/store patterns relative to SP as stack operations
- Abstracting concrete arithmetic into symbolic K notation

### Feasibility
- **tinyc `run`**: High — simple stack machine, regular patterns, clean dispatch
- **lisp `run_lisp`**: Medium — indirect dispatch breaks call graph, but body branches show node dispatch
- **mjs**: Blocked by VEX gaps (SSE/float)
- **General**: Need "state component detector" + "rule templater" as a new interpretation layer

## Terminal Emulator Subjects (evaluation needed)

Candidates for state machine extraction validation:
- **libvte** (GNOME terminal emulator library)
- **libghostty** (directory inside ghostty repo)
- **PuTTY terminal** (putty's terminal.c)
- **alacritty_terminal** or similar Rust terminal library
- Need to evaluate: VEX extractability, size, VEX gap exposure, what "golden output" means
