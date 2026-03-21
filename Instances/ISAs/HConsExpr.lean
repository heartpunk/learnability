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

/-! ## Hashable and BEq Instances

Hashable returns cached hash — O(1).
BEq uses hash fast-path, falls back to structural equality on the node. -/

instance {Reg : Type} : Hashable (HExpr Reg) where
  hash e := e.cached_hash

instance {Reg : Type} : Hashable (HMem Reg) where
  hash m := m.cached_hash

mutual
def HExprNode.beq {Reg : Type} [BEq Reg] : HExprNode Reg → HExprNode Reg → Bool
  | .const a, .const b => a == b
  | .reg a, .reg b => a == b
  | .low32 a, .low32 b => HExpr.beq a b
  | .uext32 a, .uext32 b => HExpr.beq a b
  | .sext8to32 a, .sext8to32 b => HExpr.beq a b
  | .sext32to64 a, .sext32to64 b => HExpr.beq a b
  | .sub32 a1 a2, .sub32 b1 b2 => HExpr.beq a1 b1 && HExpr.beq a2 b2
  | .shl32 a1 a2, .shl32 b1 b2 => HExpr.beq a1 b1 && HExpr.beq a2 b2
  | .and32 a1 a2, .and32 b1 b2 => HExpr.beq a1 b1 && HExpr.beq a2 b2
  | .or32 a1 a2, .or32 b1 b2 => HExpr.beq a1 b1 && HExpr.beq a2 b2
  | .xor32 a1 a2, .xor32 b1 b2 => HExpr.beq a1 b1 && HExpr.beq a2 b2
  | .add64 a1 a2, .add64 b1 b2 => HExpr.beq a1 b1 && HExpr.beq a2 b2
  | .sub64 a1 a2, .sub64 b1 b2 => HExpr.beq a1 b1 && HExpr.beq a2 b2
  | .xor64 a1 a2, .xor64 b1 b2 => HExpr.beq a1 b1 && HExpr.beq a2 b2
  | .and64 a1 a2, .and64 b1 b2 => HExpr.beq a1 b1 && HExpr.beq a2 b2
  | .or64 a1 a2, .or64 b1 b2 => HExpr.beq a1 b1 && HExpr.beq a2 b2
  | .shl64 a1 a2, .shl64 b1 b2 => HExpr.beq a1 b1 && HExpr.beq a2 b2
  | .shr64 a1 a2, .shr64 b1 b2 => HExpr.beq a1 b1 && HExpr.beq a2 b2
  | .mul64 a1 a2, .mul64 b1 b2 => HExpr.beq a1 b1 && HExpr.beq a2 b2
  | .mul32 a1 a2, .mul32 b1 b2 => HExpr.beq a1 b1 && HExpr.beq a2 b2
  | .not64 a, .not64 b => HExpr.beq a b
  | .not32 a, .not32 b => HExpr.beq a b
  | .sar64 a1 a2, .sar64 b1 b2 => HExpr.beq a1 b1 && HExpr.beq a2 b2
  | .sar32 a1 a2, .sar32 b1 b2 => HExpr.beq a1 b1 && HExpr.beq a2 b2
  | .ite a1 a2 a3, .ite b1 b2 b3 => HExpr.beq a1 b1 && HExpr.beq a2 b2 && HExpr.beq a3 b3
  | .load w1 m1 a1, .load w2 m2 a2 => w1 == w2 && HMem.beq m1 m2 && HExpr.beq a1 a2
  | _, _ => false

def HMemNode.beq {Reg : Type} [BEq Reg] : HMemNode Reg → HMemNode Reg → Bool
  | .base, .base => true
  | .store w1 m1 a1 v1, .store w2 m2 a2 v2 =>
    w1 == w2 && HMem.beq m1 m2 && HExpr.beq a1 a2 && HExpr.beq v1 v2
  | _, _ => false

def HExpr.beq {Reg : Type} [BEq Reg] : HExpr Reg → HExpr Reg → Bool
  | .mk h1 n1, .mk h2 n2 => h1 == h2 && HExprNode.beq n1 n2

def HMem.beq {Reg : Type} [BEq Reg] : HMem Reg → HMem Reg → Bool
  | .mk h1 n1, .mk h2 n2 => h1 == h2 && HMemNode.beq n1 n2
end

instance {Reg : Type} [BEq Reg] : BEq (HExpr Reg) where
  beq := HExpr.beq

instance {Reg : Type} [BEq Reg] : BEq (HMem Reg) where
  beq := HMem.beq

/-! ## Conversion to/from raw SymExpr/SymMem -/

mutual
def HExpr.toRaw {Reg : Type} : HExpr Reg → SymExpr Reg
  | .mk _ n => HExprNode.toRaw n

def HExprNode.toRaw {Reg : Type} : HExprNode Reg → SymExpr Reg
  | .const v => .const v
  | .reg r => .reg r
  | .low32 e => .low32 e.toRaw
  | .uext32 e => .uext32 e.toRaw
  | .sext8to32 e => .sext8to32 e.toRaw
  | .sext32to64 e => .sext32to64 e.toRaw
  | .sub32 l r => .sub32 l.toRaw r.toRaw
  | .shl32 l r => .shl32 l.toRaw r.toRaw
  | .and32 l r => .and32 l.toRaw r.toRaw
  | .or32 l r => .or32 l.toRaw r.toRaw
  | .xor32 l r => .xor32 l.toRaw r.toRaw
  | .add64 l r => .add64 l.toRaw r.toRaw
  | .sub64 l r => .sub64 l.toRaw r.toRaw
  | .xor64 l r => .xor64 l.toRaw r.toRaw
  | .and64 l r => .and64 l.toRaw r.toRaw
  | .or64 l r => .or64 l.toRaw r.toRaw
  | .shl64 l r => .shl64 l.toRaw r.toRaw
  | .shr64 l r => .shr64 l.toRaw r.toRaw
  | .mul64 l r => .mul64 l.toRaw r.toRaw
  | .mul32 l r => .mul32 l.toRaw r.toRaw
  | .not64 e => .not64 e.toRaw
  | .not32 e => .not32 e.toRaw
  | .sar64 l r => .sar64 l.toRaw r.toRaw
  | .sar32 l r => .sar32 l.toRaw r.toRaw
  | .ite c t f => .ite c.toRaw t.toRaw f.toRaw
  | .load w m a => .load w m.toRaw a.toRaw

def HMem.toRaw {Reg : Type} : HMem Reg → SymMem Reg
  | .mk _ n => HMemNode.toRaw n

def HMemNode.toRaw {Reg : Type} : HMemNode Reg → SymMem Reg
  | .base => .base
  | .store w m a v => .store w m.toRaw a.toRaw v.toRaw
end

mutual
def HExpr.ofRaw {Reg : Type} [Hashable Reg] : SymExpr Reg → HExpr Reg
  | .const v => HExpr.const v
  | .reg r => HExpr.reg r
  | .low32 e => HExpr.low32 (HExpr.ofRaw e)
  | .uext32 e => HExpr.uext32 (HExpr.ofRaw e)
  | .sext8to32 e => HExpr.sext8to32 (HExpr.ofRaw e)
  | .sext32to64 e => HExpr.sext32to64 (HExpr.ofRaw e)
  | .sub32 l r => HExpr.sub32 (HExpr.ofRaw l) (HExpr.ofRaw r)
  | .shl32 l r => HExpr.shl32 (HExpr.ofRaw l) (HExpr.ofRaw r)
  | .and32 l r => HExpr.and32 (HExpr.ofRaw l) (HExpr.ofRaw r)
  | .or32 l r => HExpr.or32 (HExpr.ofRaw l) (HExpr.ofRaw r)
  | .xor32 l r => HExpr.xor32 (HExpr.ofRaw l) (HExpr.ofRaw r)
  | .add64 l r => HExpr.add64 (HExpr.ofRaw l) (HExpr.ofRaw r)
  | .sub64 l r => HExpr.sub64 (HExpr.ofRaw l) (HExpr.ofRaw r)
  | .xor64 l r => HExpr.xor64 (HExpr.ofRaw l) (HExpr.ofRaw r)
  | .and64 l r => HExpr.and64 (HExpr.ofRaw l) (HExpr.ofRaw r)
  | .or64 l r => HExpr.or64 (HExpr.ofRaw l) (HExpr.ofRaw r)
  | .shl64 l r => HExpr.shl64 (HExpr.ofRaw l) (HExpr.ofRaw r)
  | .shr64 l r => HExpr.shr64 (HExpr.ofRaw l) (HExpr.ofRaw r)
  | .mul64 l r => HExpr.mul64 (HExpr.ofRaw l) (HExpr.ofRaw r)
  | .mul32 l r => HExpr.mul32 (HExpr.ofRaw l) (HExpr.ofRaw r)
  | .not64 e => HExpr.not64 (HExpr.ofRaw e)
  | .not32 e => HExpr.not32 (HExpr.ofRaw e)
  | .sar64 l r => HExpr.sar64 (HExpr.ofRaw l) (HExpr.ofRaw r)
  | .sar32 l r => HExpr.sar32 (HExpr.ofRaw l) (HExpr.ofRaw r)
  | .ite c t f => HExpr.ite (HExpr.ofRaw c) (HExpr.ofRaw t) (HExpr.ofRaw f)
  | .load w m a => HExpr.load w (HMem.ofRaw m) (HExpr.ofRaw a)

def HMem.ofRaw {Reg : Type} [Hashable Reg] : SymMem Reg → HMem Reg
  | .base => HMem.base
  | .store w m a v => HMem.store w (HMem.ofRaw m) (HExpr.ofRaw a) (HExpr.ofRaw v)
end

/-! ## Hash-Consed Substitution -/

structure HSub (Reg : Type) where
  regs : Reg → HExpr Reg
  mem : HMem Reg

def HSub.toRaw {Reg : Type} (s : HSub Reg) : SymSub Reg where
  regs r := (s.regs r).toRaw
  mem := s.mem.toRaw

def HSub.ofRaw {Reg : Type} [Hashable Reg] (s : SymSub Reg) : HSub Reg where
  regs r := HExpr.ofRaw (s.regs r)
  mem := HMem.ofRaw s.mem

/-! ## Hash-Consed Substitution with Structural Sharing

`substHExpr` substitutes through an HExpr. When children are unchanged
(detected by hash comparison + structural equality), the original node
is reused — avoiding allocation of duplicate subtrees. -/

mutual
def substHExpr {Reg : Type} [BEq Reg] (sub : HSub Reg) : HExpr Reg → HExpr Reg
  | .mk _ (.const v) => HExpr.const v
  | .mk _ (.reg r) => sub.regs r
  | .mk h (.low32 e) =>
    let e' := substHExpr sub e
    if e'.cached_hash == e.cached_hash && HExpr.beq e' e then .mk h (.low32 e) else HExpr.low32 e'
  | .mk h (.uext32 e) =>
    let e' := substHExpr sub e
    if e'.cached_hash == e.cached_hash && HExpr.beq e' e then .mk h (.uext32 e) else HExpr.uext32 e'
  | .mk h (.sext8to32 e) =>
    let e' := substHExpr sub e
    if e'.cached_hash == e.cached_hash && HExpr.beq e' e then .mk h (.sext8to32 e) else HExpr.sext8to32 e'
  | .mk h (.sext32to64 e) =>
    let e' := substHExpr sub e
    if e'.cached_hash == e.cached_hash && HExpr.beq e' e then .mk h (.sext32to64 e) else HExpr.sext32to64 e'
  | .mk h (.not64 e) =>
    let e' := substHExpr sub e
    if e'.cached_hash == e.cached_hash && HExpr.beq e' e then .mk h (.not64 e) else HExpr.not64 e'
  | .mk h (.not32 e) =>
    let e' := substHExpr sub e
    if e'.cached_hash == e.cached_hash && HExpr.beq e' e then .mk h (.not32 e) else HExpr.not32 e'
  | .mk h (.sub32 l r) =>
    let l' := substHExpr sub l; let r' := substHExpr sub r
    if l'.cached_hash == l.cached_hash && r'.cached_hash == r.cached_hash && HExpr.beq l' l && HExpr.beq r' r
    then .mk h (.sub32 l r) else HExpr.sub32 l' r'
  | .mk h (.shl32 l r) =>
    let l' := substHExpr sub l; let r' := substHExpr sub r
    if l'.cached_hash == l.cached_hash && r'.cached_hash == r.cached_hash && HExpr.beq l' l && HExpr.beq r' r
    then .mk h (.shl32 l r) else HExpr.shl32 l' r'
  | .mk h (.and32 l r) =>
    let l' := substHExpr sub l; let r' := substHExpr sub r
    if l'.cached_hash == l.cached_hash && r'.cached_hash == r.cached_hash && HExpr.beq l' l && HExpr.beq r' r
    then .mk h (.and32 l r) else HExpr.and32 l' r'
  | .mk h (.or32 l r) =>
    let l' := substHExpr sub l; let r' := substHExpr sub r
    if l'.cached_hash == l.cached_hash && r'.cached_hash == r.cached_hash && HExpr.beq l' l && HExpr.beq r' r
    then .mk h (.or32 l r) else HExpr.or32 l' r'
  | .mk h (.xor32 l r) =>
    let l' := substHExpr sub l; let r' := substHExpr sub r
    if l'.cached_hash == l.cached_hash && r'.cached_hash == r.cached_hash && HExpr.beq l' l && HExpr.beq r' r
    then .mk h (.xor32 l r) else HExpr.xor32 l' r'
  | .mk h (.add64 l r) =>
    let l' := substHExpr sub l; let r' := substHExpr sub r
    if l'.cached_hash == l.cached_hash && r'.cached_hash == r.cached_hash && HExpr.beq l' l && HExpr.beq r' r
    then .mk h (.add64 l r) else HExpr.add64 l' r'
  | .mk h (.sub64 l r) =>
    let l' := substHExpr sub l; let r' := substHExpr sub r
    if l'.cached_hash == l.cached_hash && r'.cached_hash == r.cached_hash && HExpr.beq l' l && HExpr.beq r' r
    then .mk h (.sub64 l r) else HExpr.sub64 l' r'
  | .mk h (.xor64 l r) =>
    let l' := substHExpr sub l; let r' := substHExpr sub r
    if l'.cached_hash == l.cached_hash && r'.cached_hash == r.cached_hash && HExpr.beq l' l && HExpr.beq r' r
    then .mk h (.xor64 l r) else HExpr.xor64 l' r'
  | .mk h (.and64 l r) =>
    let l' := substHExpr sub l; let r' := substHExpr sub r
    if l'.cached_hash == l.cached_hash && r'.cached_hash == r.cached_hash && HExpr.beq l' l && HExpr.beq r' r
    then .mk h (.and64 l r) else HExpr.and64 l' r'
  | .mk h (.or64 l r) =>
    let l' := substHExpr sub l; let r' := substHExpr sub r
    if l'.cached_hash == l.cached_hash && r'.cached_hash == r.cached_hash && HExpr.beq l' l && HExpr.beq r' r
    then .mk h (.or64 l r) else HExpr.or64 l' r'
  | .mk h (.shl64 l r) =>
    let l' := substHExpr sub l; let r' := substHExpr sub r
    if l'.cached_hash == l.cached_hash && r'.cached_hash == r.cached_hash && HExpr.beq l' l && HExpr.beq r' r
    then .mk h (.shl64 l r) else HExpr.shl64 l' r'
  | .mk h (.shr64 l r) =>
    let l' := substHExpr sub l; let r' := substHExpr sub r
    if l'.cached_hash == l.cached_hash && r'.cached_hash == r.cached_hash && HExpr.beq l' l && HExpr.beq r' r
    then .mk h (.shr64 l r) else HExpr.shr64 l' r'
  | .mk h (.mul64 l r) =>
    let l' := substHExpr sub l; let r' := substHExpr sub r
    if l'.cached_hash == l.cached_hash && r'.cached_hash == r.cached_hash && HExpr.beq l' l && HExpr.beq r' r
    then .mk h (.mul64 l r) else HExpr.mul64 l' r'
  | .mk h (.mul32 l r) =>
    let l' := substHExpr sub l; let r' := substHExpr sub r
    if l'.cached_hash == l.cached_hash && r'.cached_hash == r.cached_hash && HExpr.beq l' l && HExpr.beq r' r
    then .mk h (.mul32 l r) else HExpr.mul32 l' r'
  | .mk h (.sar64 l r) =>
    let l' := substHExpr sub l; let r' := substHExpr sub r
    if l'.cached_hash == l.cached_hash && r'.cached_hash == r.cached_hash && HExpr.beq l' l && HExpr.beq r' r
    then .mk h (.sar64 l r) else HExpr.sar64 l' r'
  | .mk h (.sar32 l r) =>
    let l' := substHExpr sub l; let r' := substHExpr sub r
    if l'.cached_hash == l.cached_hash && r'.cached_hash == r.cached_hash && HExpr.beq l' l && HExpr.beq r' r
    then .mk h (.sar32 l r) else HExpr.sar32 l' r'
  | .mk h (.ite c t f) =>
    let c' := substHExpr sub c; let t' := substHExpr sub t; let f' := substHExpr sub f
    if c'.cached_hash == c.cached_hash && t'.cached_hash == t.cached_hash && f'.cached_hash == f.cached_hash
       && HExpr.beq c' c && HExpr.beq t' t && HExpr.beq f' f
    then .mk h (.ite c t f) else HExpr.ite c' t' f'
  | .mk h (.load w m a) =>
    let m' := substHMem sub m; let a' := substHExpr sub a
    if m'.cached_hash == m.cached_hash && a'.cached_hash == a.cached_hash && HMem.beq m' m && HExpr.beq a' a
    then .mk h (.load w m a) else HExpr.load w m' a'

def substHMem {Reg : Type} [BEq Reg] (sub : HSub Reg) : HMem Reg → HMem Reg
  | .mk _ .base => sub.mem
  | .mk h (.store w m a v) =>
    let m' := substHMem sub m; let a' := substHExpr sub a; let v' := substHExpr sub v
    if m'.cached_hash == m.cached_hash && a'.cached_hash == a.cached_hash && v'.cached_hash == v.cached_hash
       && HMem.beq m' m && HExpr.beq a' a && HExpr.beq v' v
    then .mk h (.store w m a v) else HMem.store w m' a' v'
end

def composeHSub {Reg : Type} [BEq Reg] (sub₁ sub₂ : HSub Reg) : HSub Reg where
  regs r := substHExpr sub₁ (sub₂.regs r)
  mem := substHMem sub₁ sub₂.mem

/-! ## Bridge Theorems: toRaw ∘ ofRaw = id -/

mutual
theorem HExpr.toRaw_ofRaw {Reg : Type} [Hashable Reg] :
    (e : SymExpr Reg) → (HExpr.ofRaw e).toRaw = e
  | .const _ => rfl
  | .reg _ => rfl
  | .low32 e => congrArg SymExpr.low32 (HExpr.toRaw_ofRaw e)
  | .uext32 e => congrArg SymExpr.uext32 (HExpr.toRaw_ofRaw e)
  | .sext8to32 e => congrArg SymExpr.sext8to32 (HExpr.toRaw_ofRaw e)
  | .sext32to64 e => congrArg SymExpr.sext32to64 (HExpr.toRaw_ofRaw e)
  | .not64 e => congrArg SymExpr.not64 (HExpr.toRaw_ofRaw e)
  | .not32 e => congrArg SymExpr.not32 (HExpr.toRaw_ofRaw e)
  | .sub32 l r => congrArg₂ SymExpr.sub32 (HExpr.toRaw_ofRaw l) (HExpr.toRaw_ofRaw r)
  | .shl32 l r => congrArg₂ SymExpr.shl32 (HExpr.toRaw_ofRaw l) (HExpr.toRaw_ofRaw r)
  | .and32 l r => congrArg₂ SymExpr.and32 (HExpr.toRaw_ofRaw l) (HExpr.toRaw_ofRaw r)
  | .or32 l r => congrArg₂ SymExpr.or32 (HExpr.toRaw_ofRaw l) (HExpr.toRaw_ofRaw r)
  | .xor32 l r => congrArg₂ SymExpr.xor32 (HExpr.toRaw_ofRaw l) (HExpr.toRaw_ofRaw r)
  | .add64 l r => congrArg₂ SymExpr.add64 (HExpr.toRaw_ofRaw l) (HExpr.toRaw_ofRaw r)
  | .sub64 l r => congrArg₂ SymExpr.sub64 (HExpr.toRaw_ofRaw l) (HExpr.toRaw_ofRaw r)
  | .xor64 l r => congrArg₂ SymExpr.xor64 (HExpr.toRaw_ofRaw l) (HExpr.toRaw_ofRaw r)
  | .and64 l r => congrArg₂ SymExpr.and64 (HExpr.toRaw_ofRaw l) (HExpr.toRaw_ofRaw r)
  | .or64 l r => congrArg₂ SymExpr.or64 (HExpr.toRaw_ofRaw l) (HExpr.toRaw_ofRaw r)
  | .shl64 l r => congrArg₂ SymExpr.shl64 (HExpr.toRaw_ofRaw l) (HExpr.toRaw_ofRaw r)
  | .shr64 l r => congrArg₂ SymExpr.shr64 (HExpr.toRaw_ofRaw l) (HExpr.toRaw_ofRaw r)
  | .mul64 l r => congrArg₂ SymExpr.mul64 (HExpr.toRaw_ofRaw l) (HExpr.toRaw_ofRaw r)
  | .mul32 l r => congrArg₂ SymExpr.mul32 (HExpr.toRaw_ofRaw l) (HExpr.toRaw_ofRaw r)
  | .sar64 l r => congrArg₂ SymExpr.sar64 (HExpr.toRaw_ofRaw l) (HExpr.toRaw_ofRaw r)
  | .sar32 l r => congrArg₂ SymExpr.sar32 (HExpr.toRaw_ofRaw l) (HExpr.toRaw_ofRaw r)
  | .ite c t f => by
      show SymExpr.ite (HExpr.ofRaw c).toRaw (HExpr.ofRaw t).toRaw (HExpr.ofRaw f).toRaw = _
      rw [HExpr.toRaw_ofRaw c, HExpr.toRaw_ofRaw t, HExpr.toRaw_ofRaw f]
  | .load w m a => by
      show SymExpr.load w (HMem.ofRaw m).toRaw (HExpr.ofRaw a).toRaw = _
      rw [HMem.toRaw_ofRaw m, HExpr.toRaw_ofRaw a]

theorem HMem.toRaw_ofRaw {Reg : Type} [Hashable Reg] :
    (m : SymMem Reg) → (HMem.ofRaw m).toRaw = m
  | .base => rfl
  | .store w m a v => by
      show SymMem.store w (HMem.ofRaw m).toRaw (HExpr.ofRaw a).toRaw (HExpr.ofRaw v).toRaw = _
      rw [HMem.toRaw_ofRaw m, HExpr.toRaw_ofRaw a, HExpr.toRaw_ofRaw v]
end

/-! ## beq soundness: beq = true → toRaw equal

Requires DecidableEq Reg (not just BEq) so that reg equality is lawful. -/

set_option maxHeartbeats 800000 in
mutual
theorem HExprNode.beq_true_toRaw {Reg : Type} [DecidableEq Reg]
    (n1 n2 : HExprNode Reg) (h : HExprNode.beq n1 n2 = true) :
    HExprNode.toRaw n1 = HExprNode.toRaw n2 := by
  cases n1 <;> cases n2
  -- Pass 1: close cross-constructor cases via kernel reduction (beq = false)
  all_goals (first | contradiction | skip)
  -- Pass 2: simplify hypothesis and goal for same-constructor cases
  all_goals (simp [HExprNode.beq, Bool.and_eq_true] at h)
  all_goals (simp only [HExprNode.toRaw])
  -- Pass 3: close leaf cases (const, reg) where simp substituted equality
  all_goals (first | (simp [h]) | skip)
  -- Pass 4: apply IH to close remaining same-constructor recursive goals.
  -- Each branch destructures h in the shape needed and applies IH.
  all_goals first
    -- unary: h is a single HExpr.beq = true
    | exact HExpr.beq_true_toRaw _ _ h
    -- binary: h is (beq₁ ∧ beq₂)
    | (obtain ⟨h1, h2⟩ := h
       exact ⟨HExpr.beq_true_toRaw _ _ h1, HExpr.beq_true_toRaw _ _ h2⟩)
    -- ternary (ite): h is ((beq₁ ∧ beq₂) ∧ beq₃)
    | (obtain ⟨⟨h1, h2⟩, h3⟩ := h
       exact ⟨HExpr.beq_true_toRaw _ _ h1, HExpr.beq_true_toRaw _ _ h2, HExpr.beq_true_toRaw _ _ h3⟩)
    -- load: h is ((w_eq ∧ mem_beq) ∧ expr_beq), Width already subst'd
    | (obtain ⟨⟨_, hm⟩, ha⟩ := h
       exact ⟨HMem.beq_true_toRaw _ _ hm, HExpr.beq_true_toRaw _ _ ha⟩)

theorem HExpr.beq_true_toRaw {Reg : Type} [DecidableEq Reg]
    (e1 e2 : HExpr Reg) (h : HExpr.beq e1 e2 = true) :
    e1.toRaw = e2.toRaw := by
  match e1, e2 with
  | .mk _ n1, .mk _ n2 =>
    simp [HExpr.beq, Bool.and_eq_true] at h
    simp [HExpr.toRaw]
    exact HExprNode.beq_true_toRaw n1 n2 h.2

theorem HMem.beq_true_toRaw {Reg : Type} [DecidableEq Reg]
    (m1 m2 : HMem Reg) (h : HMem.beq m1 m2 = true) :
    m1.toRaw = m2.toRaw := by
  match m1, m2 with
  | .mk _ n1, .mk _ n2 =>
    simp [HMem.beq, Bool.and_eq_true] at h
    simp [HMem.toRaw]
    exact HMemNode.beq_true_toRaw n1 n2 h.2

theorem HMemNode.beq_true_toRaw {Reg : Type} [DecidableEq Reg]
    (n1 n2 : HMemNode Reg) (h : HMemNode.beq n1 n2 = true) :
    HMemNode.toRaw n1 = HMemNode.toRaw n2 := by
  match n1, n2 with
  | .base, .base => rfl
  | .store w1 m1 a1 v1, .store w2 m2 a2 v2 =>
    simp [HMemNode.beq, Bool.and_eq_true] at h
    obtain ⟨⟨⟨hw, hm⟩, ha⟩, hv⟩ := h
    simp [HMemNode.toRaw, hw]
    exact ⟨HMem.beq_true_toRaw _ _ hm, HExpr.beq_true_toRaw _ _ ha, HExpr.beq_true_toRaw _ _ hv⟩
  | .base, .store _ _ _ _ => simp [HMemNode.beq] at h
  | .store _ _ _ _, .base => simp [HMemNode.beq] at h
end

end VexISA
