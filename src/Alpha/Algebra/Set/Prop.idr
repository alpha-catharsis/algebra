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
PropPrfTy : (a -> Bool) -> SetPrfTy a
PropPrfTy f x = f x = True

public export
prop : (pty: a -> Bool) -> Set (PropPrfTy pty)
prop f x = decEq (f x) True
