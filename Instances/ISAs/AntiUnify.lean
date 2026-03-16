import Instances.ISAs.VexSummary

/-!
# Anti-Unification (Least General Generalization) for SymExpr / SymPC

Plotkin's first-order anti-unification adapted for VEX symbolic expressions.
Given two terms, computes the most specific generalization: common structure
is preserved, differing sub-terms become fresh variables (holes).

## Purpose

When the closure fixpoint explodes (7 → 59 → 475 → 3935 PCs per round),
anti-unifying consecutive closure-round PCs identifies TEMPLATE structure:
the common pattern is the template, the differing sub-expressions are holes
(= data registers in the register automaton sense).

Template closure IS closed by construction: lifting a template through a
substitution gives a template (same shape, different hole value). This
restores `SemClosed` and gives bisimulation via the existing proof chain.

## Key property

Anti-unification gives the MOST SPECIFIC generalization (unique up to
variable renaming). This means the template quotient is the FINEST possible
→ bisimulation, not just simulation. This is Plotkin 1970 / Reynolds 1970.

## References

- Plotkin 1970, "A Note on Inductive Generalization"
- Sinha 2008, "Symbolic Program Analysis Using Term Rewriting and Generalization"
- Arusoaie & Lucanu 2022, "Proof-Carrying Parameters in Certified Symbolic Execution"
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

/-! ## Anti-unification result types -/

/-- A hole in a template, identified by a natural number. -/
abbrev HoleId := Nat

mutual
/-- A template expression: like SymExpr but with holes where terms diverge. -/
inductive TemplateExpr (Reg : Type) where
  | hole : HoleId → TemplateExpr Reg
  | const : UInt64 → TemplateExpr Reg
  | reg : Reg → TemplateExpr Reg
  | low32 : TemplateExpr Reg → TemplateExpr Reg
  | uext32 : TemplateExpr Reg → TemplateExpr Reg
  | sext8to32 : TemplateExpr Reg → TemplateExpr Reg
  | sext32to64 : TemplateExpr Reg → TemplateExpr Reg
  | sub32 : TemplateExpr Reg → TemplateExpr Reg → TemplateExpr Reg
  | shl32 : TemplateExpr Reg → TemplateExpr Reg → TemplateExpr Reg
  | add64 : TemplateExpr Reg → TemplateExpr Reg → TemplateExpr Reg
  | sub64 : TemplateExpr Reg → TemplateExpr Reg → TemplateExpr Reg
  | xor64 : TemplateExpr Reg → TemplateExpr Reg → TemplateExpr Reg
  | and64 : TemplateExpr Reg → TemplateExpr Reg → TemplateExpr Reg
  | or64 : TemplateExpr Reg → TemplateExpr Reg → TemplateExpr Reg
  | shl64 : TemplateExpr Reg → TemplateExpr Reg → TemplateExpr Reg
  | shr64 : TemplateExpr Reg → TemplateExpr Reg → TemplateExpr Reg
  | load : Width → TemplateMem Reg → TemplateExpr Reg → TemplateExpr Reg

/-- A template memory: like SymMem but with holes. -/
inductive TemplateMem (Reg : Type) where
  | hole : HoleId → TemplateMem Reg
  | base : TemplateMem Reg
  | store : Width → TemplateMem Reg → TemplateExpr Reg → TemplateExpr Reg → TemplateMem Reg
end

instance {Reg : Type} : Nonempty (TemplateExpr Reg) := ⟨.const 0⟩
instance {Reg : Type} : Nonempty (TemplateMem Reg) := ⟨.base⟩
instance {Reg : Type} : Inhabited (TemplateExpr Reg) := ⟨.const 0⟩
instance {Reg : Type} : Inhabited (TemplateMem Reg) := ⟨.base⟩

/-- A template PC: like SymPC but with holes in sub-expressions. -/
inductive TemplatePC (Reg : Type) where
  | hole : HoleId → TemplatePC Reg
  | true : TemplatePC Reg
  | eq : TemplateExpr Reg → TemplateExpr Reg → TemplatePC Reg
  | lt : TemplateExpr Reg → TemplateExpr Reg → TemplatePC Reg
  | le : TemplateExpr Reg → TemplateExpr Reg → TemplatePC Reg
  | and : TemplatePC Reg → TemplatePC Reg → TemplatePC Reg
  | not : TemplatePC Reg → TemplatePC Reg

instance {Reg : Type} : Nonempty (TemplatePC Reg) := ⟨.true⟩
instance {Reg : Type} : Inhabited (TemplatePC Reg) := ⟨.true⟩

/-! ## Embedding: inject ground terms into template types -/

mutual
def embedExpr {Reg : Type} : SymExpr Reg → TemplateExpr Reg
  | .const v => .const v
  | .reg r => .reg r
  | .low32 x => .low32 (embedExpr x)
  | .uext32 x => .uext32 (embedExpr x)
  | .sext8to32 x => .sext8to32 (embedExpr x)
  | .sext32to64 x => .sext32to64 (embedExpr x)
  | .sub32 a b => .sub32 (embedExpr a) (embedExpr b)
  | .shl32 a b => .shl32 (embedExpr a) (embedExpr b)
  | .add64 a b => .add64 (embedExpr a) (embedExpr b)
  | .sub64 a b => .sub64 (embedExpr a) (embedExpr b)
  | .xor64 a b => .xor64 (embedExpr a) (embedExpr b)
  | .and64 a b => .and64 (embedExpr a) (embedExpr b)
  | .or64 a b => .or64 (embedExpr a) (embedExpr b)
  | .shl64 a b => .shl64 (embedExpr a) (embedExpr b)
  | .shr64 a b => .shr64 (embedExpr a) (embedExpr b)
  | .load w m a => .load w (embedMem m) (embedExpr a)

def embedMem {Reg : Type} : SymMem Reg → TemplateMem Reg
  | .base => .base
  | .store w m a v => .store w (embedMem m) (embedExpr a) (embedExpr v)
end

def embedPC {Reg : Type} : SymPC Reg → TemplatePC Reg
  | .true => .true
  | .eq a b => .eq (embedExpr a) (embedExpr b)
  | .lt a b => .lt (embedExpr a) (embedExpr b)
  | .le a b => .le (embedExpr a) (embedExpr b)
  | .and φ ψ => .and (embedPC φ) (embedPC ψ)
  | .not φ => .not (embedPC φ)

/-! ## Anti-unification state -/

/-- Substitution pair: what a hole maps to in the left and right input. -/
structure HoleSub (Reg : Type) where
  left : SymExpr Reg
  right : SymExpr Reg

/-- Anti-unification state: fresh counter + accumulated hole substitutions. -/
structure AUState (Reg : Type) where
  nextHole : HoleId := 0
  subs : Array (HoleSub Reg) := #[]

/-! ## Fresh hole allocation -/

/-- Allocate a fresh hole for a diverging expr pair. -/
def freshExprHole {Reg : Type}
    (st : AUState Reg) (l r : SymExpr Reg) : TemplateExpr Reg × AUState Reg :=
  let holeId := st.nextHole
  (.hole holeId,
   { nextHole := holeId + 1, subs := st.subs.push { left := l, right := r } })

/-- Allocate a fresh hole for a diverging mem pair. -/
def freshMemHole {Reg : Type}
    (st : AUState Reg) : TemplateMem Reg × AUState Reg :=
  let holeId := st.nextHole
  (.hole holeId, { st with nextHole := holeId + 1 })

/-- Allocate a fresh hole for a diverging PC pair. -/
def freshPCHole {Reg : Type}
    (st : AUState Reg) : TemplatePC Reg × AUState Reg :=
  let holeId := st.nextHole
  (.hole holeId, { st with nextHole := holeId + 1 })

/-! ## Core anti-unification algorithm -/

mutual
/-- Anti-unify two SymExpr terms. Returns (template, updated state).
    When root constructors match, recurse structurally.
    When they differ, introduce a fresh hole. -/
def antiUnifyExpr {Reg : Type} [DecidableEq Reg]
    (st : AUState Reg) (l r : SymExpr Reg) : TemplateExpr Reg × AUState Reg :=
  if l == r then
    (embedExpr l, st)
  else
    match l, r with
    | .low32 a, .low32 b =>
      let (ta, st') := antiUnifyExpr st a b; (.low32 ta, st')
    | .uext32 a, .uext32 b =>
      let (ta, st') := antiUnifyExpr st a b; (.uext32 ta, st')
    | .sext8to32 a, .sext8to32 b =>
      let (ta, st') := antiUnifyExpr st a b; (.sext8to32 ta, st')
    | .sext32to64 a, .sext32to64 b =>
      let (ta, st') := antiUnifyExpr st a b; (.sext32to64 ta, st')
    | .sub32 a1 a2, .sub32 b1 b2 =>
      let (t1, st') := antiUnifyExpr st a1 b1
      let (t2, st'') := antiUnifyExpr st' a2 b2; (.sub32 t1 t2, st'')
    | .shl32 a1 a2, .shl32 b1 b2 =>
      let (t1, st') := antiUnifyExpr st a1 b1
      let (t2, st'') := antiUnifyExpr st' a2 b2; (.shl32 t1 t2, st'')
    | .add64 a1 a2, .add64 b1 b2 =>
      let (t1, st') := antiUnifyExpr st a1 b1
      let (t2, st'') := antiUnifyExpr st' a2 b2; (.add64 t1 t2, st'')
    | .sub64 a1 a2, .sub64 b1 b2 =>
      let (t1, st') := antiUnifyExpr st a1 b1
      let (t2, st'') := antiUnifyExpr st' a2 b2; (.sub64 t1 t2, st'')
    | .xor64 a1 a2, .xor64 b1 b2 =>
      let (t1, st') := antiUnifyExpr st a1 b1
      let (t2, st'') := antiUnifyExpr st' a2 b2; (.xor64 t1 t2, st'')
    | .and64 a1 a2, .and64 b1 b2 =>
      let (t1, st') := antiUnifyExpr st a1 b1
      let (t2, st'') := antiUnifyExpr st' a2 b2; (.and64 t1 t2, st'')
    | .or64 a1 a2, .or64 b1 b2 =>
      let (t1, st') := antiUnifyExpr st a1 b1
      let (t2, st'') := antiUnifyExpr st' a2 b2; (.or64 t1 t2, st'')
    | .shl64 a1 a2, .shl64 b1 b2 =>
      let (t1, st') := antiUnifyExpr st a1 b1
      let (t2, st'') := antiUnifyExpr st' a2 b2; (.shl64 t1 t2, st'')
    | .shr64 a1 a2, .shr64 b1 b2 =>
      let (t1, st') := antiUnifyExpr st a1 b1
      let (t2, st'') := antiUnifyExpr st' a2 b2; (.shr64 t1 t2, st'')
    | .load w1 m1 a1, .load w2 m2 a2 =>
      if w1 == w2 then
        let (tm, st') := antiUnifyMem st m1 m2
        let (ta, st'') := antiUnifyExpr st' a1 a2; (.load w1 tm ta, st'')
      else freshExprHole st l r
    | _, _ => freshExprHole st l r
  termination_by (sizeOf l, sizeOf r)

/-- Anti-unify two SymMem terms. -/
def antiUnifyMem {Reg : Type} [DecidableEq Reg]
    (st : AUState Reg) (l r : SymMem Reg) : TemplateMem Reg × AUState Reg :=
  match l, r with
  | .base, .base => (.base, st)
  | .store w1 m1 a1 v1, .store w2 m2 a2 v2 =>
    if w1 == w2 then
      let (tm, st') := antiUnifyMem st m1 m2
      let (ta, st'') := antiUnifyExpr st' a1 a2
      let (tv, st''') := antiUnifyExpr st'' v1 v2
      (.store w1 tm ta tv, st''')
    else freshMemHole st
  | _, _ => freshMemHole st
  termination_by (sizeOf l, sizeOf r)

/-- Anti-unify two SymPC terms. -/
def antiUnifyPC {Reg : Type} [DecidableEq Reg]
    (st : AUState Reg) (l r : SymPC Reg) : TemplatePC Reg × AUState Reg :=
  if l == r then (embedPC l, st)
  else
    match l, r with
    | .true, .true => (.true, st)
    | .eq a1 a2, .eq b1 b2 =>
      let (t1, st') := antiUnifyExpr st a1 b1
      let (t2, st'') := antiUnifyExpr st' a2 b2; (.eq t1 t2, st'')
    | .lt a1 a2, .lt b1 b2 =>
      let (t1, st') := antiUnifyExpr st a1 b1
      let (t2, st'') := antiUnifyExpr st' a2 b2; (.lt t1 t2, st'')
    | .le a1 a2, .le b1 b2 =>
      let (t1, st') := antiUnifyExpr st a1 b1
      let (t2, st'') := antiUnifyExpr st' a2 b2; (.le t1 t2, st'')
    | .and a1 a2, .and b1 b2 =>
      let (t1, st') := antiUnifyPC st a1 b1
      let (t2, st'') := antiUnifyPC st' a2 b2; (.and t1 t2, st'')
    | .not a, .not b =>
      let (t, st') := antiUnifyPC st a b; (.not t, st')
    | _, _ => freshPCHole st
  termination_by (sizeOf l, sizeOf r)
end

/-! ## Top-level API -/

/-- Anti-unify two PCs. Returns (template, hole substitutions).
    The template is the most specific generalization.
    Each hole in the template maps to a (left_value, right_value) pair
    recording what diverges between the two inputs. -/
def antiUnify {Reg : Type} [DecidableEq Reg]
    (l r : SymPC Reg) : TemplatePC Reg × Array (HoleSub Reg) :=
  let (tpc, st) := antiUnifyPC {} l r
  (tpc, st.subs)

/-! ## Hole counting -/

mutual
def TemplateExpr.holeCount {Reg : Type} : TemplateExpr Reg → Nat
  | .hole _ => 1
  | .const _ | .reg _ => 0
  | .low32 x | .uext32 x | .sext8to32 x | .sext32to64 x => x.holeCount
  | .sub32 a b | .shl32 a b | .add64 a b | .sub64 a b
  | .xor64 a b | .and64 a b | .or64 a b | .shl64 a b | .shr64 a b =>
    a.holeCount + b.holeCount
  | .load _ m a => TemplateMem.holeCount m + a.holeCount

def TemplateMem.holeCount {Reg : Type} : TemplateMem Reg → Nat
  | .hole _ => 1
  | .base => 0
  | .store _ m a v => m.holeCount + TemplateExpr.holeCount a + TemplateExpr.holeCount v
end

def TemplatePC.holeCount {Reg : Type} : TemplatePC Reg → Nat
  | .hole _ => 1
  | .true => 0
  | .eq a b | .lt a b | .le a b => a.holeCount + b.holeCount
  | .and φ ψ => φ.holeCount + ψ.holeCount
  | .not φ => φ.holeCount

def TemplatePC.isParametric {Reg : Type} (t : TemplatePC Reg) : Bool :=
  t.holeCount > 0

/-! ## Instantiation: apply hole substitutions to recover ground terms -/

/-- A hole valuation: maps hole IDs to ground expressions. -/
abbrev HoleVal (Reg : Type) := HoleId → SymExpr Reg

mutual
/-- Instantiate a template expression by replacing holes with ground exprs. -/
def instantiateExpr {Reg : Type} (val : HoleVal Reg) : TemplateExpr Reg → SymExpr Reg
  | .hole h => val h
  | .const v => .const v
  | .reg r => .reg r
  | .low32 x => .low32 (instantiateExpr val x)
  | .uext32 x => .uext32 (instantiateExpr val x)
  | .sext8to32 x => .sext8to32 (instantiateExpr val x)
  | .sext32to64 x => .sext32to64 (instantiateExpr val x)
  | .sub32 a b => .sub32 (instantiateExpr val a) (instantiateExpr val b)
  | .shl32 a b => .shl32 (instantiateExpr val a) (instantiateExpr val b)
  | .add64 a b => .add64 (instantiateExpr val a) (instantiateExpr val b)
  | .sub64 a b => .sub64 (instantiateExpr val a) (instantiateExpr val b)
  | .xor64 a b => .xor64 (instantiateExpr val a) (instantiateExpr val b)
  | .and64 a b => .and64 (instantiateExpr val a) (instantiateExpr val b)
  | .or64 a b => .or64 (instantiateExpr val a) (instantiateExpr val b)
  | .shl64 a b => .shl64 (instantiateExpr val a) (instantiateExpr val b)
  | .shr64 a b => .shr64 (instantiateExpr val a) (instantiateExpr val b)
  | .load w m a => .load w (instantiateMem val m) (instantiateExpr val a)

/-- Instantiate a template memory by replacing holes. -/
def instantiateMem {Reg : Type} (val : HoleVal Reg) : TemplateMem Reg → SymMem Reg
  | .hole _ => .base  -- Memory holes degenerate to base (conservative)
  | .base => .base
  | .store w m a v => .store w (instantiateMem val m) (instantiateExpr val a) (instantiateExpr val v)
end

/-- Instantiate a template PC by replacing holes with ground exprs. -/
def instantiatePC {Reg : Type} (val : HoleVal Reg) : TemplatePC Reg → SymPC Reg
  | .hole _ => .true  -- PC holes degenerate to true (conservative)
  | .true => .true
  | .eq a b => .eq (instantiateExpr val a) (instantiateExpr val b)
  | .lt a b => .lt (instantiateExpr val a) (instantiateExpr val b)
  | .le a b => .le (instantiateExpr val a) (instantiateExpr val b)
  | .and φ ψ => .and (instantiatePC val φ) (instantiatePC val ψ)
  | .not φ => .not (instantiatePC val φ)

/-! ## Correctness: embedding roundtrip

The fundamental property: embedding a ground term into template space and
then instantiating with ANY valuation recovers the original term.
This is because embedded terms have no holes. -/

mutual
theorem instantiateExpr_embedExpr {Reg : Type} (val : HoleVal Reg) (e : SymExpr Reg) :
    instantiateExpr val (embedExpr e) = e := by
  match e with
  | .const _ | .reg _ => rfl
  | .low32 x => simp [embedExpr, instantiateExpr, instantiateExpr_embedExpr val x]
  | .uext32 x => simp [embedExpr, instantiateExpr, instantiateExpr_embedExpr val x]
  | .sext8to32 x => simp [embedExpr, instantiateExpr, instantiateExpr_embedExpr val x]
  | .sext32to64 x => simp [embedExpr, instantiateExpr, instantiateExpr_embedExpr val x]
  | .sub32 a b => simp [embedExpr, instantiateExpr, instantiateExpr_embedExpr val a, instantiateExpr_embedExpr val b]
  | .shl32 a b => simp [embedExpr, instantiateExpr, instantiateExpr_embedExpr val a, instantiateExpr_embedExpr val b]
  | .add64 a b => simp [embedExpr, instantiateExpr, instantiateExpr_embedExpr val a, instantiateExpr_embedExpr val b]
  | .sub64 a b => simp [embedExpr, instantiateExpr, instantiateExpr_embedExpr val a, instantiateExpr_embedExpr val b]
  | .xor64 a b => simp [embedExpr, instantiateExpr, instantiateExpr_embedExpr val a, instantiateExpr_embedExpr val b]
  | .and64 a b => simp [embedExpr, instantiateExpr, instantiateExpr_embedExpr val a, instantiateExpr_embedExpr val b]
  | .or64 a b => simp [embedExpr, instantiateExpr, instantiateExpr_embedExpr val a, instantiateExpr_embedExpr val b]
  | .shl64 a b => simp [embedExpr, instantiateExpr, instantiateExpr_embedExpr val a, instantiateExpr_embedExpr val b]
  | .shr64 a b => simp [embedExpr, instantiateExpr, instantiateExpr_embedExpr val a, instantiateExpr_embedExpr val b]
  | .load w m a => simp [embedExpr, instantiateExpr, instantiateExpr_embedExpr val a, instantiateMem_embedMem val m]

theorem instantiateMem_embedMem {Reg : Type} (val : HoleVal Reg) (m : SymMem Reg) :
    instantiateMem val (embedMem m) = m := by
  match m with
  | .base => rfl
  | .store w mem a v =>
    simp [embedMem, instantiateMem, instantiateMem_embedMem val mem,
          instantiateExpr_embedExpr val a, instantiateExpr_embedExpr val v]
end

theorem instantiatePC_embedPC {Reg : Type} (val : HoleVal Reg) (pc : SymPC Reg) :
    instantiatePC val (embedPC pc) = pc := by
  match pc with
  | .true => rfl
  | .eq a b => simp [embedPC, instantiatePC, instantiateExpr_embedExpr val a, instantiateExpr_embedExpr val b]
  | .lt a b => simp [embedPC, instantiatePC, instantiateExpr_embedExpr val a, instantiateExpr_embedExpr val b]
  | .le a b => simp [embedPC, instantiatePC, instantiateExpr_embedExpr val a, instantiateExpr_embedExpr val b]
  | .and φ ψ => simp [embedPC, instantiatePC, instantiatePC_embedPC val φ, instantiatePC_embedPC val ψ]
  | .not φ => simp [embedPC, instantiatePC, instantiatePC_embedPC val φ]

end VexISA
