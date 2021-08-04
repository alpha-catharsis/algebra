---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.PropSet

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

------------------
-- Proposition set
------------------

public export
PropSetPrf : (a -> Bool) -> SetFpt a
PropSetPrf f x = (f x = True)

public export
propSet : (f : a -> Bool) -> SetFn (PropSetPrf f)
propSet f x = decEq (f x) True
