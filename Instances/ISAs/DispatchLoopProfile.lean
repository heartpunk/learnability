import Instances.ISAs.VexCompTree
import Instances.ISAs.VexProofCompression
import Instances.ISAs.DispatchLoopEval

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA VexIRParser

/-!
# DispatchLoopProfile — Synthetic block profiling harness

Generates randomized synthetic blocks with controlled parameters to isolate
performance factors in the stabilization computation. Each run prints its
seed for reproducibility.

## Parameters varied:
- **N**: number of blocks (controls |bodyDenot|)
- **branchWidth**: number of exit guards per block (0 = linear, 1-3 = branching)
- **exprDepth**: depth of SymExpr trees in register assignments
- **regSpread**: how many distinct registers are written per block

Results written to `.lake/profile.log` for `tail -f`.
-/

/-! ## Simple LCG PRNG -/

structure RNG where
  state : UInt64
  deriving Repr

def RNG.mk (seed : UInt64) : RNG := ⟨seed⟩

def RNG.next (rng : RNG) : RNG × UInt64 :=
  -- LCG: state' = 6364136223846793005 * state + 1442695040888963407
  let s := 6364136223846793005 * rng.state + 1442695040888963407
  (⟨s⟩, s)

def RNG.nextBounded (rng : RNG) (bound : UInt64) : RNG × UInt64 :=
  let (rng', v) := rng.next
  if bound == 0 then (rng', 0) else (rng', v % bound)

def RNG.nextNat (rng : RNG) (bound : Nat) : RNG × Nat :=
  let (rng', v) := rng.nextBounded (UInt64.ofNat bound)
  (rng', v.toNat)

/-! ## Synthetic block generation -/

/-- Pick a register from a small pool based on index. -/
def pickReg (idx : Nat) : Amd64Reg :=
  match idx % 6 with
  | 0 => .rax | 1 => .rcx | 2 => .rdx
  | 3 => .rsi | 4 => .rdi | 5 => .rbp
  | _ => .rax

/-- Generate a random expression of given depth. -/
partial def genExpr (rng : RNG) (depth : Nat) : RNG × Expr Amd64Reg :=
  if depth == 0 then
    let (rng, choice) := rng.nextNat 3
    match choice with
    | 0 => let (rng, v) := rng.nextBounded 256; (rng, .const v)
    | 1 => let (rng, r) := rng.nextNat 6; (rng, .get (pickReg r))
    | _ => let (rng, t) := rng.nextNat 8; (rng, .tmp t)
  else
    let (rng, choice) := rng.nextNat 4
    match choice with
    | 0 =>
      let (rng, l) := genExpr rng (depth - 1)
      let (rng, r) := genExpr rng (depth - 1)
      (rng, .add64 l r)
    | 1 =>
      let (rng, l) := genExpr rng (depth - 1)
      let (rng, r) := genExpr rng (depth - 1)
      (rng, .sub64 l r)
    | 2 =>
      let (rng, l) := genExpr rng (depth - 1)
      let (rng, r) := genExpr rng (depth - 1)
      (rng, .and64 l r)
    | _ =>
      let (rng, e) := genExpr rng (depth - 1)
      (rng, .shl64 e (.const 2))

/-- Generate a random condition. -/
def genCond (rng : RNG) (exprDepth : Nat) : RNG × Cond Amd64Reg :=
  let (rng, choice) := rng.nextNat 3
  let (rng, l) := genExpr rng exprDepth
  let (rng, r) := genExpr rng exprDepth
  match choice with
  | 0 => (rng, .eq64 l r)
  | 1 => (rng, .lt64 l r)
  | _ => (rng, .le64 l r)

/-- Generate a synthetic block with controlled parameters.
    - `branchWidth`: number of exit guards (0 = purely linear)
    - `exprDepth`: depth of generated expressions
    - `regSpread`: number of distinct registers written
    - `addr`: block address (used for rip guard) -/
def genBlock (rng : RNG) (branchWidth exprDepth regSpread : Nat) (addr : UInt64) :
    RNG × Block Amd64Reg := Id.run do
  let mut rng := rng
  let mut stmts : List (Stmt Amd64Reg) := []
  -- Generate register writes
  for i in List.range regSpread do
    let reg := pickReg i
    let (rng', expr) := genExpr rng exprDepth
    rng := rng'
    stmts := stmts ++ [Stmt.put reg expr]
  -- Generate branch exits
  for _ in List.range branchWidth do
    let (rng', cond) := genCond rng exprDepth
    rng := rng'
    let (rng'', target) := rng'.nextBounded 0x10000
    rng := rng''
    stmts := stmts ++ [Stmt.exit cond target]
  -- Final rip write for fallthrough
  stmts := stmts ++ [Stmt.put .rip (.const 0)]
  (rng, { stmts := stmts, ip_reg := .rip, next := 0 })

/-- Generate N synthetic blocks with given parameters, each at a distinct address. -/
def genBlocks (rng : RNG) (n branchWidth exprDepth regSpread : Nat) :
    RNG × List (UInt64 × Block Amd64Reg) := Id.run do
  let mut rng := rng
  let mut blocks : List (UInt64 × Block Amd64Reg) := []
  for i in List.range n do
    let addr := UInt64.ofNat (0x1000 + i * 0x100)
    let (rng', block) := genBlock rng branchWidth exprDepth regSpread addr
    rng := rng'
    blocks := blocks ++ [(addr, block)]
  (rng, blocks)

/-! ## Profiling harness -/

/-- Run a single profiling trial: build bodyDenot, stabilize, measure. -/
def profileTrial (log : IO.FS.Handle) (seed : UInt64)
    (n branchWidth exprDepth regSpread : Nat) : IO Unit := do
  let rng := RNG.mk seed
  let (_, blocks) := genBlocks rng n branchWidth exprDepth regSpread
  let t0 ← IO.monoMsNow
  let body := flatBodyDenot Amd64Reg.rip blocks
  let t1 ← IO.monoMsNow
  let logPath : System.FilePath := ".lake/profile.log"
  match ← computeStabilization body 200 logPath with
  | some (k, card) =>
    let t2 ← IO.monoMsNow
    let line := s!"{seed}, {n}, {branchWidth}, {exprDepth}, {regSpread}, {body.card}, {k}, {card}, {t1 - t0}, {t2 - t1}"
    log.putStrLn line
    log.flush
  | none =>
    let t2 ← IO.monoMsNow
    let line := s!"{seed}, {n}, {branchWidth}, {exprDepth}, {regSpread}, {body.card}, DNF, DNF, {t1 - t0}, {t2 - t1}"
    log.putStrLn line
    log.flush

#eval do
  let logPath : System.FilePath := ".lake/profile.log"
  let log ← IO.FS.Handle.mk logPath .write
  log.putStrLn "seed, N, branchWidth, exprDepth, regSpread, bodyDenot, K, S_final, bodyDenot_ms, stabilization_ms"
  log.flush
  -- Use system time as base seed
  let baseSeed ← IO.monoMsNow
  IO.println s!"=== Profile Harness === base_seed={baseSeed}"
  log.putStrLn s!"# base_seed={baseSeed}"
  log.flush
  -- Sweep: vary N with different block shapes
  -- m=3 trials per (N, shape) combination
  let m := 3
  for n in [3, 5, 8, 10] do
    for branchWidth in [0, 1, 2] do
      for exprDepth in [0, 1, 2] do
        let regSpread := 3  -- fix regSpread for now
        for trial in List.range m do
          let seed := UInt64.ofNat (baseSeed.toNat + n * 1000 + branchWidth * 100 + exprDepth * 10 + trial)
          IO.println s!"  N={n} bw={branchWidth} ed={exprDepth} trial={trial} seed={seed}"
          profileTrial log seed n branchWidth exprDepth regSpread
  IO.println "=== Profile complete ==="
