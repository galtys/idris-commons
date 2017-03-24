-- ------------------------------------------------------------ [ Literals.idr ]
||| Module    : Literals.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| Deal with literal values at the type-level.
module Data.Literals

%default total
%access public export

||| Proof that the given value `val'` of type `ty` has value `a`.
Literal : (ty : Type) -> (a : ty) -> Type
Literal valTy val = (val' : valTy ** val' = val)

||| Representation of String literals.
LitString : String -> Type
LitString str = Literal String str

||| Proof that the given natural is the successor of `n`.
Next : (n : Nat) -> Type
Next n = (o : Nat ** o = S n)

-- --------------------------------------------------------------------- [ EOF ]
