import Instances.ISAs.VexSummary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VexISA

/-! # Hash-Consed Expression Types

Hash-consed wrappers around SymExpr/SymMem. Every node caches its hash,
giving O(1) hashing and fast-path equality. Children in `HExprNode` are
`HExpr` (wrapped), so pattern matching always has access to cached hashes.
-/

mutual
inductive HExprNode (Reg : Type) where
  | const : UInt64 → HExprNode Reg
  | reg : Reg → HExprNode Reg
  | low32 : HExpr Reg → HExprNode Reg
  | uext32 : HExpr Reg → HExprNode Reg
  | sext8to32 : HExpr Reg → HExprNode Reg
  | sext32to64 : HExpr Reg → HExprNode Reg
  | sub32 : HExpr Reg → HExpr Reg → HExprNode Reg
  | shl32 : HExpr Reg → HExpr Reg → HExprNode Reg
  | and32 : HExpr Reg → HExpr Reg → HExprNode Reg
  | or32 : HExpr Reg → HExpr Reg → HExprNode Reg
  | xor32 : HExpr Reg → HExpr Reg → HExprNode Reg
  | add64 : HExpr Reg → HExpr Reg → HExprNode Reg
  | sub64 : HExpr Reg → HExpr Reg → HExprNode Reg
  | xor64 : HExpr Reg → HExpr Reg → HExprNode Reg
  | and64 : HExpr Reg → HExpr Reg → HExprNode Reg
  | or64 : HExpr Reg → HExpr Reg → HExprNode Reg
  | shl64 : HExpr Reg → HExpr Reg → HExprNode Reg
  | shr64 : HExpr Reg → HExpr Reg → HExprNode Reg
  | mul64 : HExpr Reg → HExpr Reg → HExprNode Reg
  | mul32 : HExpr Reg → HExpr Reg → HExprNode Reg
  | not64 : HExpr Reg → HExprNode Reg
  | not32 : HExpr Reg → HExprNode Reg
  | sar64 : HExpr Reg → HExpr Reg → HExprNode Reg
  | sar32 : HExpr Reg → HExpr Reg → HExprNode Reg
  | ite : HExpr Reg → HExpr Reg → HExpr Reg → HExprNode Reg
  | load : Width → HMem Reg → HExpr Reg → HExprNode Reg

inductive HMemNode (Reg : Type) where
  | base : HMemNode Reg
  | store : Width → HMem Reg → HExpr Reg → HExpr Reg → HMemNode Reg

inductive HExpr (Reg : Type) where
  | mk : UInt64 → HExprNode Reg → HExpr Reg

inductive HMem (Reg : Type) where
  | mk : UInt64 → HMemNode Reg → HMem Reg
end

/-! ## Accessors -/

def HExpr.cached_hash {Reg : Type} : HExpr Reg → UInt64
  | .mk h _ => h

def HExpr.node {Reg : Type} : HExpr Reg → HExprNode Reg
  | .mk _ n => n

def HMem.cached_hash {Reg : Type} : HMem Reg → UInt64
  | .mk h _ => h

def HMem.node {Reg : Type} : HMem Reg → HMemNode Reg
  | .mk _ n => n

/-! ## Smart Constructors

Each computes hash from children's cached hashes — O(1).
Tag numbers match `hashSymExprD` for consistency. -/

namespace HExpr

def const {Reg : Type} (v : UInt64) : HExpr Reg :=
  .mk (mixHash 1 (hash v)) (.const v)

def reg {Reg : Type} [Hashable Reg] (r : Reg) : HExpr Reg :=
  .mk (mixHash 2 (hash r)) (.reg r)

def low32 {Reg : Type} (e : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 3 e.cached_hash) (.low32 e)

def uext32 {Reg : Type} (e : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 4 e.cached_hash) (.uext32 e)

def sext8to32 {Reg : Type} (e : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 5 e.cached_hash) (.sext8to32 e)

def sext32to64 {Reg : Type} (e : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 6 e.cached_hash) (.sext32to64 e)

def sub32 {Reg : Type} (l r : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 7 (mixHash l.cached_hash r.cached_hash)) (.sub32 l r)

def shl32 {Reg : Type} (l r : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 8 (mixHash l.cached_hash r.cached_hash)) (.shl32 l r)

def and32 {Reg : Type} (l r : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 17 (mixHash l.cached_hash r.cached_hash)) (.and32 l r)

def or32 {Reg : Type} (l r : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 41 (mixHash l.cached_hash r.cached_hash)) (.or32 l r)

def xor32 {Reg : Type} (l r : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 41 (mixHash l.cached_hash r.cached_hash)) (.xor32 l r)

def add64 {Reg : Type} (l r : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 9 (mixHash l.cached_hash r.cached_hash)) (.add64 l r)

def sub64 {Reg : Type} (l r : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 10 (mixHash l.cached_hash r.cached_hash)) (.sub64 l r)

def xor64 {Reg : Type} (l r : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 11 (mixHash l.cached_hash r.cached_hash)) (.xor64 l r)

def and64 {Reg : Type} (l r : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 12 (mixHash l.cached_hash r.cached_hash)) (.and64 l r)

def or64 {Reg : Type} (l r : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 13 (mixHash l.cached_hash r.cached_hash)) (.or64 l r)

def shl64 {Reg : Type} (l r : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 14 (mixHash l.cached_hash r.cached_hash)) (.shl64 l r)

def shr64 {Reg : Type} (l r : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 15 (mixHash l.cached_hash r.cached_hash)) (.shr64 l r)

def mul64 {Reg : Type} (l r : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 42 (mixHash l.cached_hash r.cached_hash)) (.mul64 l r)

def mul32 {Reg : Type} (l r : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 43 (mixHash l.cached_hash r.cached_hash)) (.mul32 l r)

def not64 {Reg : Type} (e : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 44 e.cached_hash) (.not64 e)

def not32 {Reg : Type} (e : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 45 e.cached_hash) (.not32 e)

def sar64 {Reg : Type} (l r : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 46 (mixHash l.cached_hash r.cached_hash)) (.sar64 l r)

def sar32 {Reg : Type} (l r : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 47 (mixHash l.cached_hash r.cached_hash)) (.sar32 l r)

def ite {Reg : Type} (c t f : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 48 (mixHash c.cached_hash (mixHash t.cached_hash f.cached_hash))) (.ite c t f)

def load {Reg : Type} (w : Width) (m : HMem Reg) (addr : HExpr Reg) : HExpr Reg :=
  .mk (mixHash 16 (mixHash (hash w.byteCount) (mixHash m.cached_hash addr.cached_hash))) (.load w m addr)

end HExpr

namespace HMem

def base {Reg : Type} : HMem Reg :=
  .mk 17 .base

def store {Reg : Type} (w : Width) (m : HMem Reg) (addr val : HExpr Reg) : HMem Reg :=
  .mk (mixHash 18 (mixHash (hash w.byteCount) (mixHash m.cached_hash (mixHash addr.cached_hash val.cached_hash)))) (.store w m addr val)

end HMem

end VexISA
