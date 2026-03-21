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

end VexISA
