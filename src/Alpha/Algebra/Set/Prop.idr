---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Prop

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

------------------
-- Proposition Set
------------------

public export
prop : (f: a -> Bool) -> Set a
prop f = MkSet (\x => f x = True) (\x => decEq (f x) True)
