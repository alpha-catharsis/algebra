---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Nat

-------------------
-- External imports
-------------------

import Data.Nat

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Equal
import Alpha.Algebra.Rel.Prop
import Alpha.Algebra.Rel.Rel

---------------
-- LTE relation
---------------

public export
data LTE : Type where
  MkLTE : LTE

public export
lte : LTE
lte = MkLTE

public export
0 LTEPrf : RelPrfTy Nat Nat
LTEPrf (x,y) = Nat.LTE x y

public export
Rel LTE Nat Nat where
  RelPrf _ = LTEPrf

public export
DecRel LTE Nat Nat where
  areRelated _ x y = isLTE x y

-----------------
-- LTE properties
-----------------

public export
RelRefl LTE Nat where
  relRefl _ = reflexive {ty=Nat} {rel=LTE}

public export
RelAntiSymm LTE Nat where
  relAntiSymmEq _ = EqlPrf
  relAntiSymm _ = antisymmetric {rel=LTE} {x} {y}

public export
RelTrans LTE Nat where
  relTrans _ = transitive {rel=LTE} {x} {y} {z}
