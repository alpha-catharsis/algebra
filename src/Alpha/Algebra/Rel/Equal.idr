---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Equal

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Prop
import Alpha.Algebra.Rel.Rel

---------------
-- LTE relation
---------------

public export
data Eql : Type -> Type -> Type where
  MkEql : (0 a : Type) -> (0 b : Type) -> Eql a b

public export
eql : (0 a : Type) -> (0 b : Type) -> Eql a b
eql = MkEql

public export
homEql : (0 a : Type) -> Eql a a
homEql a = MkEql a a

public export
0 EqlPrf : RelPrfTy a b
EqlPrf (x,y) = x = y

public export
Rel (Eql a b) a b where
  RelPrf (MkEql a b) = EqlPrf

public export
DecEq a => DecRel (Eql a a) a a where
  areRelated (MkEql a a) x y = decEq x y

-----------------
-- Equal properties
-----------------

public export
RelRefl (Eql a a) a where
  relRefl (MkEql a a) = Refl

public export
RelSymm (Eql a a) a where
  relSymm (MkEql a a) prf = sym prf

public export
RelTrans (Eql a a) a where
  relTrans (MkEql a a) lprf rprf = rewrite lprf in rprf
