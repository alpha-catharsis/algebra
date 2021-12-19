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

-----------------
-- Equal relation
-----------------

public export
0 EqualRel : (a : Type) -> (b : Type) -> Rel a b
EqualRel _ _ (x,y) = x = y

public export
equal : DecEq a => DecRel (EqualRel a a)
equal (x,y) = decEq x y

-------------------
-- Equal properties
-------------------

public export
0 equalRefl : relRefl (EqualRel a a)
equalRefl = Refl

public export
0 equalSymm : relSymm (EqualRel a a)
equalSymm Refl = Refl

public export
0 equalTrans : relTrans (EqualRel a a)
equalTrans lprf rprf = rewrite lprf in rprf
