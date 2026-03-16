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

/-- A template memory: like SymMem but expressions may have holes.
    No mem-level holes — when mem structures don't match, the caller
    falls back to an expr-level hole for the entire load. -/
inductive TemplateMem (Reg : Type) where
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

/-- Allocate a fresh hole for a diverging PC pair.
    Pushes a dummy entry to subs to maintain `nextHole = subs.size`. -/
def freshPCHole {Reg : Type}
    (st : AUState Reg) : TemplatePC Reg × AUState Reg :=
  let holeId := st.nextHole
  (.hole holeId,
   { nextHole := holeId + 1, subs := st.subs.push { left := .const 0, right := .const 0 } })

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
        match antiUnifyMem st m1 m2 with
        | none => freshExprHole st l r
        | some (tm, st') =>
          let (ta, st'') := antiUnifyExpr st' a1 a2; (.load w1 tm ta, st'')
      else freshExprHole st l r
    | _, _ => freshExprHole st l r
  termination_by (sizeOf l, sizeOf r)

/-- Anti-unify two SymMem terms. Returns `none` when mem structures
    don't match (different widths, base vs store). Caller falls back
    to expr-level hole. -/
def antiUnifyMem {Reg : Type} [DecidableEq Reg]
    (st : AUState Reg) (l r : SymMem Reg) : Option (TemplateMem Reg × AUState Reg) :=
  match l, r with
  | .base, .base => some (.base, st)
  | .store w1 m1 a1 v1, .store w2 m2 a2 v2 =>
    if w1 == w2 then
      match antiUnifyMem st m1 m2 with
      | none => none
      | some (tm, st') =>
        let (ta, st'') := antiUnifyExpr st' a1 a2
        let (tv, st''') := antiUnifyExpr st'' v1 v2
        some (.store w1 tm ta tv, st''')
    else none
  | _, _ => none
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

/-- Instantiate a template memory by replacing expr holes within it. -/
def instantiateMem {Reg : Type} (val : HoleVal Reg) : TemplateMem Reg → SymMem Reg
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

/-! ## Generalization correctness

The core theorem: `antiUnify` produces a valid generalization.
Given `(template, subs) = antiUnify l r`:
- `instantiateExpr (leftVal subs) template = l`  (left projection)
- `instantiateExpr (rightVal subs) template = r`  (right projection)

where `leftVal subs h = subs[h]!.left` and `rightVal subs h = subs[h]!.right`.

This is the property that makes anti-unification a GENERALIZATION:
the template with the left substitution recovers the left input,
and similarly for the right. Combined with most-specificity (which
follows from the algorithm only introducing holes when necessary),
this makes it a least general generalization (LGG). -/

/-- Extract left valuation from AU state: hole h ↦ subs[h].left. -/
def AUState.leftVal {Reg : Type} (st : AUState Reg) : HoleVal Reg :=
  fun h =>
    if h_lt : h < st.subs.size then (st.subs[h]).left else .const 0

/-- Extract right valuation from AU state: hole h ↦ subs[h].right. -/
def AUState.rightVal {Reg : Type} (st : AUState Reg) : HoleVal Reg :=
  fun h =>
    if h_lt : h < st.subs.size then (st.subs[h]).right else .const 0

/-! ## State monotonicity

Anti-unification only extends the state: `nextHole` grows monotonically and
`subs` only gets appended to. This is the key invariant for the correctness
proof: holes created by earlier recursive calls remain valid in later states. -/

/-- State extension: st₂ extends st₁ (subs only appended, nextHole only grows). -/
structure AUState.Extends {Reg : Type} (st₁ st₂ : AUState Reg) : Prop where
  nextHole_le : st₁.nextHole ≤ st₂.nextHole
  subs_prefix : st₁.subs.size ≤ st₂.subs.size
  subs_agree : ∀ (h : Nat), (h_lt : h < st₁.subs.size) →
    st₂.subs[h]'(Nat.lt_of_lt_of_le h_lt subs_prefix) = st₁.subs[h]

theorem AUState.Extends.refl {Reg : Type} (st : AUState Reg) :
    AUState.Extends st st :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => rfl⟩

theorem AUState.Extends.trans {Reg : Type} {st₁ st₂ st₃ : AUState Reg}
    (h₁₂ : AUState.Extends st₁ st₂) (h₂₃ : AUState.Extends st₂ st₃) :
    AUState.Extends st₁ st₃ where
  nextHole_le := Nat.le_trans h₁₂.nextHole_le h₂₃.nextHole_le
  subs_prefix := Nat.le_trans h₁₂.subs_prefix h₂₃.subs_prefix
  subs_agree h h_lt := by
    rw [h₂₃.subs_agree h (Nat.lt_of_lt_of_le h_lt h₁₂.subs_prefix)]
    exact h₁₂.subs_agree h h_lt

/-- freshExprHole extends the state by exactly one entry. -/
theorem freshExprHole_extends {Reg : Type}
    (st : AUState Reg) (l r : SymExpr Reg) :
    AUState.Extends st (freshExprHole st l r).2 where
  nextHole_le := Nat.le_succ _
  subs_prefix := by simp [freshExprHole, Array.size_push]
  subs_agree h h_lt := by
    simp [freshExprHole]
    rw [Array.getElem_push]
    split
    · rfl
    · omega

/-- freshPCHole extends the state by one dummy entry. -/
theorem freshPCHole_extends {Reg : Type}
    (st : AUState Reg) :
    AUState.Extends st (freshPCHole st).2 where
  nextHole_le := Nat.le_succ _
  subs_prefix := by simp [freshPCHole, Array.size_push]
  subs_agree h h_lt := by
    simp [freshPCHole]
    rw [Array.getElem_push]
    split
    · rfl
    · omega

/-! ## Valuation agreement under state extension

If all holes in a template were created before state extension,
then instantiation with the old vs new state gives the same result. -/

mutual
/-- All holes in a template expression have ID < n. -/
def TemplateExpr.holesBelow {Reg : Type} (n : Nat) : TemplateExpr Reg → Prop
  | .hole h => h < n
  | .const _ | .reg _ => True
  | .low32 x | .uext32 x | .sext8to32 x | .sext32to64 x => x.holesBelow n
  | .sub32 a b | .shl32 a b | .add64 a b | .sub64 a b
  | .xor64 a b | .and64 a b | .or64 a b | .shl64 a b | .shr64 a b =>
    a.holesBelow n ∧ b.holesBelow n
  | .load _ m a => TemplateMem.holesBelow n m ∧ a.holesBelow n

def TemplateMem.holesBelow {Reg : Type} (n : Nat) : TemplateMem Reg → Prop
  | .base => True
  | .store _ m a v => m.holesBelow n ∧ TemplateExpr.holesBelow n a ∧ TemplateExpr.holesBelow n v
end

def TemplatePC.holesBelow {Reg : Type} (n : Nat) : TemplatePC Reg → Prop
  | .hole h => h < n
  | .true => True
  | .eq a b | .lt a b | .le a b => a.holesBelow n ∧ b.holesBelow n
  | .and φ ψ => φ.holesBelow n ∧ ψ.holesBelow n
  | .not φ => φ.holesBelow n

mutual
/-- Embedded expressions have no holes (all holes below 0). -/
theorem embedExpr_holesBelow {Reg : Type} (e : SymExpr Reg) (n : Nat) :
    (embedExpr e).holesBelow n := by
  match e with
  | .const _ | .reg _ => trivial
  | .low32 x => exact embedExpr_holesBelow x n
  | .uext32 x => exact embedExpr_holesBelow x n
  | .sext8to32 x => exact embedExpr_holesBelow x n
  | .sext32to64 x => exact embedExpr_holesBelow x n
  | .sub32 a b => exact ⟨embedExpr_holesBelow a n, embedExpr_holesBelow b n⟩
  | .shl32 a b => exact ⟨embedExpr_holesBelow a n, embedExpr_holesBelow b n⟩
  | .add64 a b => exact ⟨embedExpr_holesBelow a n, embedExpr_holesBelow b n⟩
  | .sub64 a b => exact ⟨embedExpr_holesBelow a n, embedExpr_holesBelow b n⟩
  | .xor64 a b => exact ⟨embedExpr_holesBelow a n, embedExpr_holesBelow b n⟩
  | .and64 a b => exact ⟨embedExpr_holesBelow a n, embedExpr_holesBelow b n⟩
  | .or64 a b => exact ⟨embedExpr_holesBelow a n, embedExpr_holesBelow b n⟩
  | .shl64 a b => exact ⟨embedExpr_holesBelow a n, embedExpr_holesBelow b n⟩
  | .shr64 a b => exact ⟨embedExpr_holesBelow a n, embedExpr_holesBelow b n⟩
  | .load _ m a => exact ⟨embedMem_holesBelow m n, embedExpr_holesBelow a n⟩

theorem embedMem_holesBelow {Reg : Type} (m : SymMem Reg) (n : Nat) :
    (embedMem m).holesBelow n := by
  match m with
  | .base => trivial
  | .store _ mem a v =>
    exact ⟨embedMem_holesBelow mem n, embedExpr_holesBelow a n, embedExpr_holesBelow v n⟩
end

mutual
/-- If two valuations agree on all holes below n, instantiation agrees on
    templates with holes below n. -/
theorem instantiateExpr_val_agree {Reg : Type} {n : Nat}
    {val₁ val₂ : HoleVal Reg} (t : TemplateExpr Reg)
    (h_below : t.holesBelow n)
    (h_agree : ∀ h, h < n → val₁ h = val₂ h) :
    instantiateExpr val₁ t = instantiateExpr val₂ t := by
  match t with
  | .hole h => exact h_agree h h_below
  | .const _ | .reg _ => rfl
  | .low32 x =>
    simp [instantiateExpr]; exact instantiateExpr_val_agree x h_below h_agree
  | .uext32 x =>
    simp [instantiateExpr]; exact instantiateExpr_val_agree x h_below h_agree
  | .sext8to32 x =>
    simp [instantiateExpr]; exact instantiateExpr_val_agree x h_below h_agree
  | .sext32to64 x =>
    simp [instantiateExpr]; exact instantiateExpr_val_agree x h_below h_agree
  | .sub32 a b =>
    simp [instantiateExpr]
    exact ⟨instantiateExpr_val_agree a h_below.1 h_agree,
           instantiateExpr_val_agree b h_below.2 h_agree⟩
  | .shl32 a b =>
    simp [instantiateExpr]
    exact ⟨instantiateExpr_val_agree a h_below.1 h_agree,
           instantiateExpr_val_agree b h_below.2 h_agree⟩
  | .add64 a b =>
    simp [instantiateExpr]
    exact ⟨instantiateExpr_val_agree a h_below.1 h_agree,
           instantiateExpr_val_agree b h_below.2 h_agree⟩
  | .sub64 a b =>
    simp [instantiateExpr]
    exact ⟨instantiateExpr_val_agree a h_below.1 h_agree,
           instantiateExpr_val_agree b h_below.2 h_agree⟩
  | .xor64 a b =>
    simp [instantiateExpr]
    exact ⟨instantiateExpr_val_agree a h_below.1 h_agree,
           instantiateExpr_val_agree b h_below.2 h_agree⟩
  | .and64 a b =>
    simp [instantiateExpr]
    exact ⟨instantiateExpr_val_agree a h_below.1 h_agree,
           instantiateExpr_val_agree b h_below.2 h_agree⟩
  | .or64 a b =>
    simp [instantiateExpr]
    exact ⟨instantiateExpr_val_agree a h_below.1 h_agree,
           instantiateExpr_val_agree b h_below.2 h_agree⟩
  | .shl64 a b =>
    simp [instantiateExpr]
    exact ⟨instantiateExpr_val_agree a h_below.1 h_agree,
           instantiateExpr_val_agree b h_below.2 h_agree⟩
  | .shr64 a b =>
    simp [instantiateExpr]
    exact ⟨instantiateExpr_val_agree a h_below.1 h_agree,
           instantiateExpr_val_agree b h_below.2 h_agree⟩
  | .load _ m a =>
    simp [instantiateExpr]
    exact ⟨instantiateMem_val_agree m h_below.1 h_agree,
           instantiateExpr_val_agree a h_below.2 h_agree⟩

theorem instantiateMem_val_agree {Reg : Type} {n : Nat}
    {val₁ val₂ : HoleVal Reg} (t : TemplateMem Reg)
    (h_below : t.holesBelow n)
    (h_agree : ∀ h, h < n → val₁ h = val₂ h) :
    instantiateMem val₁ t = instantiateMem val₂ t := by
  match t with
  | .base => rfl
  | .store _ m a v =>
    simp [instantiateMem]
    exact ⟨instantiateMem_val_agree m h_below.1 h_agree,
           instantiateExpr_val_agree a h_below.2.1 h_agree,
           instantiateExpr_val_agree v h_below.2.2 h_agree⟩
end

/-! ## Generalization correctness: freshExprHole

When `freshExprHole` creates a hole, the resulting state has the input
terms at the hole index. -/

/-- Well-formed state: nextHole tracks subs array size. -/
def AUState.Aligned {Reg : Type} (st : AUState Reg) : Prop :=
  st.nextHole = st.subs.size

theorem AUState.Aligned.init {Reg : Type} :
    AUState.Aligned (Reg := Reg) {} := rfl

theorem freshExprHole_aligned {Reg : Type} (st : AUState Reg) (l r : SymExpr Reg)
    (h_al : st.Aligned) : (freshExprHole st l r).2.Aligned := by
  unfold AUState.Aligned at *; simp [freshExprHole, Array.size_push, h_al]

theorem freshPCHole_aligned {Reg : Type} (st : AUState Reg)
    (h_al : st.Aligned) : (freshPCHole st).2.Aligned := by
  unfold AUState.Aligned at *; simp [freshPCHole, Array.size_push, h_al]

theorem freshExprHole_left {Reg : Type}
    (st : AUState Reg) (l r : SymExpr Reg) (h_al : st.Aligned) :
    let result := freshExprHole st l r
    instantiateExpr result.2.leftVal result.1 = l := by
  show (fun h =>
    if h_lt : h < (st.subs.push { left := l, right := r }).size
    then ((st.subs.push { left := l, right := r })[h]).left
    else .const 0) st.nextHole = l
  rw [h_al]
  simp [Array.size_push, Array.getElem_push]

theorem freshExprHole_right {Reg : Type}
    (st : AUState Reg) (l r : SymExpr Reg) (h_al : st.Aligned) :
    let result := freshExprHole st l r
    instantiateExpr result.2.rightVal result.1 = r := by
  show (fun h =>
    if h_lt : h < (st.subs.push { left := l, right := r }).size
    then ((st.subs.push { left := l, right := r })[h]).right
    else .const 0) st.nextHole = r
  rw [h_al]
  simp [Array.size_push, Array.getElem_push]

/-! ## Main correctness theorem — structures

Bundle the properties we need from antiUnifyExpr/Mem into compound
correctness predicates for the mutual well-founded induction. -/

/-- Compound correctness property for antiUnifyExpr.
    Given `(t, st') = antiUnifyExpr st l r`:
    - State alignment is preserved
    - State only extends (monotonicity)
    - Left instantiation recovers `l`
    - Right instantiation recovers `r` -/
structure AntiUnifyExprCorrect {Reg : Type} (st : AUState Reg)
    (l r : SymExpr Reg) (t : TemplateExpr Reg) (st' : AUState Reg) : Prop where
  aligned : st.Aligned → st'.Aligned
  extends_ : AUState.Extends st st'
  left_correct : st.Aligned → instantiateExpr st'.leftVal t = l
  right_correct : st.Aligned → instantiateExpr st'.rightVal t = r

/-- Compound correctness property for antiUnifyMem. -/
structure AntiUnifyMemCorrect {Reg : Type} (st : AUState Reg)
    (l r : SymMem Reg) (t : TemplateMem Reg) (st' : AUState Reg) : Prop where
  aligned : st.Aligned → st'.Aligned
  extends_ : AUState.Extends st st'

/-! ## Correctness proof via well-founded induction

The main theorem: antiUnifyExpr/Mem produce valid generalizations.
We prove this by well-founded induction on (sizeOf l + sizeOf r),
matching the termination measure of the functions. -/

/-- freshExprHole produces a correct result (base case for diverging terms). -/
theorem freshExprHole_correct {Reg : Type}
    (st : AUState Reg) (l r : SymExpr Reg) :
    AntiUnifyExprCorrect st l r (freshExprHole st l r).1 (freshExprHole st l r).2 where
  aligned h_al := freshExprHole_aligned st l r h_al
  extends_ := freshExprHole_extends st l r
  left_correct h_al := freshExprHole_left st l r h_al
  right_correct h_al := freshExprHole_right st l r h_al

/-- State extension preserves left valuation for earlier holes.
    If st₁ extends to st₂, then st₂.leftVal agrees with st₁.leftVal
    on all holes < st₁.subs.size. -/
theorem AUState.Extends.leftVal_agree {Reg : Type}
    {st₁ st₂ : AUState Reg} (h_ext : AUState.Extends st₁ st₂)
    (h : Nat) (h_lt : h < st₁.subs.size) :
    st₂.leftVal h = st₁.leftVal h := by
  unfold AUState.leftVal
  have h_lt₂ := Nat.lt_of_lt_of_le h_lt h_ext.subs_prefix
  simp [h_lt, h_lt₂]
  exact congrArg HoleSub.left (h_ext.subs_agree h h_lt)

/-- Same for right valuation. -/
theorem AUState.Extends.rightVal_agree {Reg : Type}
    {st₁ st₂ : AUState Reg} (h_ext : AUState.Extends st₁ st₂)
    (h : Nat) (h_lt : h < st₁.subs.size) :
    st₂.rightVal h = st₁.rightVal h := by
  unfold AUState.rightVal
  have h_lt₂ := Nat.lt_of_lt_of_le h_lt h_ext.subs_prefix
  simp [h_lt, h_lt₂]
  exact congrArg HoleSub.right (h_ext.subs_agree h h_lt)

/-- If template holes are below st₁.subs.size and st₁ extends to st₂,
    left instantiation is invariant. -/
theorem instantiateExpr_extends_left {Reg : Type}
    {st₁ st₂ : AUState Reg} (h_ext : AUState.Extends st₁ st₂)
    (t : TemplateExpr Reg) (h_below : t.holesBelow st₁.subs.size) :
    instantiateExpr st₂.leftVal t = instantiateExpr st₁.leftVal t :=
  instantiateExpr_val_agree t h_below (fun h h_lt => h_ext.leftVal_agree h h_lt)

/-- Same for right instantiation. -/
theorem instantiateExpr_extends_right {Reg : Type}
    {st₁ st₂ : AUState Reg} (h_ext : AUState.Extends st₁ st₂)
    (t : TemplateExpr Reg) (h_below : t.holesBelow st₁.subs.size) :
    instantiateExpr st₂.rightVal t = instantiateExpr st₁.rightVal t :=
  instantiateExpr_val_agree t h_below (fun h h_lt => h_ext.rightVal_agree h h_lt)

/-- antiUnifyExpr output has holes below st'.subs.size when state is aligned.
    This is needed for the inductive step: sub-results from the first
    recursive call have holes bounded by the intermediate state, so they
    remain valid after the second recursive call extends the state further. -/

-- For the full mutual induction, we need holesBelow for antiUnifyExpr output.
-- Statement (proof is the next milestone):
-- holesBelow for freshExprHole
theorem freshExprHole_holesBelow {Reg : Type}
    (st : AUState Reg) (l r : SymExpr Reg) (h_al : st.Aligned) :
    (freshExprHole st l r).1.holesBelow (freshExprHole st l r).2.subs.size := by
  unfold AUState.Aligned at h_al
  simp [freshExprHole, TemplateExpr.holesBelow, Array.size_push, h_al]

-- holesBelow monotonicity: if holes below n and n ≤ m, then holes below m
mutual
theorem TemplateExpr.holesBelow_mono {Reg : Type} {n m : Nat}
    (t : TemplateExpr Reg) (h : t.holesBelow n) (h_le : n ≤ m) :
    t.holesBelow m := by
  match t with
  | .hole h' => exact Nat.lt_of_lt_of_le h h_le
  | .const _ | .reg _ => trivial
  | .low32 x | .uext32 x | .sext8to32 x | .sext32to64 x =>
    exact TemplateExpr.holesBelow_mono x h h_le
  | .sub32 a b | .shl32 a b | .add64 a b | .sub64 a b
  | .xor64 a b | .and64 a b | .or64 a b | .shl64 a b | .shr64 a b =>
    exact ⟨TemplateExpr.holesBelow_mono a h.1 h_le,
           TemplateExpr.holesBelow_mono b h.2 h_le⟩
  | .load _ m' a =>
    exact ⟨TemplateMem.holesBelow_mono m' h.1 h_le,
           TemplateExpr.holesBelow_mono a h.2 h_le⟩

theorem TemplateMem.holesBelow_mono {Reg : Type} {n m : Nat}
    (t : TemplateMem Reg) (h : t.holesBelow n) (h_le : n ≤ m) :
    t.holesBelow m := by
  match t with
  | .base => trivial
  | .store _ m' a v =>
    exact ⟨TemplateMem.holesBelow_mono m' h.1 h_le,
           TemplateExpr.holesBelow_mono a h.2.1 h_le,
           TemplateExpr.holesBelow_mono v h.2.2 h_le⟩
end

-- Compound property: holesBelow + aligned + extends, for mutual induction
structure AntiUnifyExprInv {Reg : Type} (st st' : AUState Reg)
    (t : TemplateExpr Reg) : Prop where
  aligned : st.Aligned → st'.Aligned
  extends_ : AUState.Extends st st'
  holesBelow : st.Aligned → t.holesBelow st'.subs.size

/-- Compound invariant for antiUnifyMem: when it returns `some`,
    the result preserves alignment, extends state, and holes are bounded.
    When it returns `none`, no invariant needed — caller handles fallback. -/
structure AntiUnifyMemInv {Reg : Type} (st st' : AUState Reg)
    (t : TemplateMem Reg) : Prop where
  aligned : st.Aligned → st'.Aligned
  extends_ : AUState.Extends st st'
  holesBelow : st.Aligned → t.holesBelow st'.subs.size

mutual
theorem antiUnifyExpr_inv {Reg : Type} [DecidableEq Reg]
    (st : AUState Reg) (l r : SymExpr Reg) :
    AntiUnifyExprInv st (antiUnifyExpr st l r).2 (antiUnifyExpr st l r).1 := by
  unfold antiUnifyExpr
  split
  · exact ⟨id, .refl st, fun h_al => embedExpr_holesBelow l _⟩
  · rename_i h_neq
    split
    -- 4 unary: .low32, .uext32, .sext8to32, .sext32to64
    all_goals try (rename_i a b
                   have ih := antiUnifyExpr_inv st a b
                   exact ⟨ih.aligned, ih.extends_, fun h_al => ih.holesBelow h_al⟩)
    -- 9 binary: .sub32, .shl32, .add64, .sub64, .xor64, .and64, .or64, .shl64, .shr64
    all_goals try (rename_i a1 a2 b1 b2
                   have ih1 := antiUnifyExpr_inv st a1 b1
                   have ih2 := antiUnifyExpr_inv (antiUnifyExpr st a1 b1).2 a2 b2
                   exact ⟨fun h => ih2.aligned (ih1.aligned h),
                          ih1.extends_.trans ih2.extends_,
                          fun h_al => ⟨TemplateExpr.holesBelow_mono _ (ih1.holesBelow h_al) ih2.extends_.subs_prefix,
                                       ih2.holesBelow (ih1.aligned h_al)⟩⟩)
    -- .load: w match → antiUnifyMem option → antiUnifyExpr
    · split
      · -- w1 == w2: case split on antiUnifyMem result
        cases h_mem : antiUnifyMem st _ _ with
        | none =>
          -- antiUnifyMem returned none → function uses freshExprHole
          simp [h_mem]
          exact ⟨fun h => freshExprHole_aligned st _ _ h,
                 freshExprHole_extends st _ _,
                 fun h_al => freshExprHole_holesBelow st _ _ h_al⟩
        | some val =>
          obtain ⟨tm, stm⟩ := val
          sorry -- needs antiUnifyMem_inv + antiUnifyExpr_inv composition
                -- blocker: l/r args inaccessible after cases on Option match
      · exact ⟨fun h => freshExprHole_aligned st _ _ h,
               freshExprHole_extends st _ _,
               fun h_al => freshExprHole_holesBelow st _ _ h_al⟩
    -- catch-all: remaining goals are all freshExprHole
    all_goals exact ⟨fun h => freshExprHole_aligned _ _ _ h,
                      freshExprHole_extends _ _ _,
                      fun h_al => freshExprHole_holesBelow _ _ _ h_al⟩
  termination_by (sizeOf l, sizeOf r)

/-- When antiUnifyMem returns `some`, the compound invariant holds.
    Proved by matching on the inputs (for termination) and using the
    definition of antiUnifyMem to relate the match to the result. -/
theorem antiUnifyMem_inv {Reg : Type} [DecidableEq Reg]
    (st : AUState Reg) (l r : SymMem Reg) :
    ∀ tm st', antiUnifyMem st l r = some (tm, st') → AntiUnifyMemInv st st' tm := by
  intro tm st' h_some
  unfold antiUnifyMem at h_some
  cases l with
  | base =>
    cases r with
    | base =>
      simp at h_some; obtain ⟨h1, h2⟩ := h_some; subst h1; subst h2
      exact ⟨id, .refl st, fun _ => trivial⟩
    | store => simp at h_some
  | store w1 m1 a1 v1 =>
    cases r with
    | base => simp at h_some
    | store w2 m2 a2 v2 =>
      by_cases hw : (w1 == w2)
      · simp [hw] at h_some
        match h_sub : antiUnifyMem st m1 m2 with
        | none => simp [h_sub] at h_some
        | some (sub_tm, sub_st) =>
          simp [h_sub] at h_some
          obtain ⟨h1, h2⟩ := h_some; subst h1; subst h2
          have ihm := antiUnifyMem_inv st m1 m2 sub_tm sub_st h_sub
          have iha := antiUnifyExpr_inv sub_st a1 a2
          have ihv := antiUnifyExpr_inv (antiUnifyExpr sub_st a1 a2).2 v1 v2
          exact ⟨fun h => ihv.aligned (iha.aligned (ihm.aligned h)),
                 ihm.extends_.trans (iha.extends_.trans ihv.extends_),
                 fun h_al =>
                   ⟨TemplateMem.holesBelow_mono _ (ihm.holesBelow h_al)
                      (iha.extends_.trans ihv.extends_).subs_prefix,
                    TemplateExpr.holesBelow_mono _ (iha.holesBelow (ihm.aligned h_al))
                      ihv.extends_.subs_prefix,
                    ihv.holesBelow (iha.aligned (ihm.aligned h_al))⟩⟩
      · simp [hw] at h_some
  termination_by (sizeOf l, sizeOf r)
  decreasing_by
    simp_wf
    -- After simp_wf: goal is Prod.Lex (sizeOf m1, sizeOf m2) (sizeOf l, sizeOf r)
    -- where l = .store w1 m1 a1 v1 (from cases). But WF captures l before cases.
    -- We have l✝ in context equated to .store w1 m1 a1 v1 by cases.
    -- Need to unfold sizeOf l via the equation hypothesis.
    subst_vars
    simp [VexISA.SymMem.store.sizeOf_spec]
    omega
end

-- Extract individual theorems
theorem antiUnifyExpr_holesBelow {Reg : Type} [DecidableEq Reg]
    (st : AUState Reg) (l r : SymExpr Reg) (h_al : st.Aligned) :
    (antiUnifyExpr st l r).1.holesBelow (antiUnifyExpr st l r).2.subs.size :=
  (antiUnifyExpr_inv st l r).holesBelow h_al

theorem antiUnifyExpr_aligned {Reg : Type} [DecidableEq Reg]
    (st : AUState Reg) (l r : SymExpr Reg) (h_al : st.Aligned) :
    (antiUnifyExpr st l r).2.Aligned :=
  (antiUnifyExpr_inv st l r).aligned h_al

theorem antiUnifyExpr_extends {Reg : Type} [DecidableEq Reg]
    (st : AUState Reg) (l r : SymExpr Reg) :
    AUState.Extends st (antiUnifyExpr st l r).2 :=
  (antiUnifyExpr_inv st l r).extends_

-- Correctness proofs: left and right instantiation recover inputs.
-- With Option-returning antiUnifyMem, the degenerate cases disappear:
-- when antiUnifyMem returns none, the caller uses freshExprHole (already proved).
-- antiUnifyMem_left/right only need to cover the `some` case.

theorem antiUnifyExpr_left {Reg : Type} [DecidableEq Reg]
    (st : AUState Reg) (l r : SymExpr Reg) (h_al : st.Aligned) :
    instantiateExpr (antiUnifyExpr st l r).2.leftVal (antiUnifyExpr st l r).1 = l := by
  sorry

theorem antiUnifyExpr_right {Reg : Type} [DecidableEq Reg]
    (st : AUState Reg) (l r : SymExpr Reg) (h_al : st.Aligned) :
    instantiateExpr (antiUnifyExpr st l r).2.rightVal (antiUnifyExpr st l r).1 = r := by
  sorry

/-- TOP-LEVEL THEOREM: antiUnify produces a valid generalization.
    The template instantiated with left substitutions = left input. -/
theorem antiUnify_left {Reg : Type} [DecidableEq Reg]
    (l r : SymPC Reg) :
    let (template, subs) := antiUnify l r
    instantiatePC (fun h => if h_lt : h < subs.size then (subs[h]).left else .const 0) template = l := by
  sorry

/-- TOP-LEVEL THEOREM: antiUnify produces a valid generalization.
    The template instantiated with right substitutions = right input. -/
theorem antiUnify_right {Reg : Type} [DecidableEq Reg]
    (l r : SymPC Reg) :
    let (template, subs) := antiUnify l r
    instantiatePC (fun h => if h_lt : h < subs.size then (subs[h]).right else .const 0) template = r := by
  sorry

/-! ## Template substitution: apply a SymSub to a template

Holes pass through unchanged. Non-hole sub-expressions get substituted
as normal SymExpr/SymMem terms via the existing substSymExpr/substSymMem. -/

mutual
def substTemplateExpr {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (σ : SymSub Reg) : TemplateExpr Reg → TemplateExpr Reg
  | .hole h => .hole h  -- holes are inert under substitution
  | .const v => embedExpr (substSymExpr σ (.const v))
  | .reg r => embedExpr (substSymExpr σ (.reg r))
  | .low32 x => .low32 (substTemplateExpr σ x)
  | .uext32 x => .uext32 (substTemplateExpr σ x)
  | .sext8to32 x => .sext8to32 (substTemplateExpr σ x)
  | .sext32to64 x => .sext32to64 (substTemplateExpr σ x)
  | .sub32 a b => .sub32 (substTemplateExpr σ a) (substTemplateExpr σ b)
  | .shl32 a b => .shl32 (substTemplateExpr σ a) (substTemplateExpr σ b)
  | .add64 a b => .add64 (substTemplateExpr σ a) (substTemplateExpr σ b)
  | .sub64 a b => .sub64 (substTemplateExpr σ a) (substTemplateExpr σ b)
  | .xor64 a b => .xor64 (substTemplateExpr σ a) (substTemplateExpr σ b)
  | .and64 a b => .and64 (substTemplateExpr σ a) (substTemplateExpr σ b)
  | .or64 a b => .or64 (substTemplateExpr σ a) (substTemplateExpr σ b)
  | .shl64 a b => .shl64 (substTemplateExpr σ a) (substTemplateExpr σ b)
  | .shr64 a b => .shr64 (substTemplateExpr σ a) (substTemplateExpr σ b)
  | .load w m a => .load w (substTemplateMem σ m) (substTemplateExpr σ a)

def substTemplateMem {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (σ : SymSub Reg) : TemplateMem Reg → TemplateMem Reg
  | .base => embedMem (substSymMem σ .base)
  | .store w m a v => .store w (substTemplateMem σ m) (substTemplateExpr σ a) (substTemplateExpr σ v)
end

def substTemplatePC {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (σ : SymSub Reg) : TemplatePC Reg → TemplatePC Reg
  | .hole h => .hole h
  | .true => .true
  | .eq a b => .eq (substTemplateExpr σ a) (substTemplateExpr σ b)
  | .lt a b => .lt (substTemplateExpr σ a) (substTemplateExpr σ b)
  | .le a b => .le (substTemplateExpr σ a) (substTemplateExpr σ b)
  | .and φ ψ => .and (substTemplatePC σ φ) (substTemplatePC σ ψ)
  | .not φ => .not (substTemplatePC σ φ)

/-! ## Left distributivity: σ(t₁ ↓ t₂) = σt₁ ↓ σt₂

The key property for SemClosed: lifting a template through a branch
substitution gives back a template. Proved by structural induction. -/

-- Statement (proof is the goal):
theorem leftDistributivity_PC {Reg : Type} [DecidableEq Reg] [Fintype Reg]
    (σ : SymSub Reg) (pc₁ pc₂ : SymPC Reg) :
    substTemplatePC σ (antiUnifyPC {} pc₁ pc₂).1 =
    (antiUnifyPC {} (substSymPC σ pc₁) (substSymPC σ pc₂)).1 := by
  sorry

end VexISA
