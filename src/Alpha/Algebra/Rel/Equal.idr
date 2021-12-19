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

