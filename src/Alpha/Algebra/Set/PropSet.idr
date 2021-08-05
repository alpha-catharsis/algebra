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
PropSetFpt : (a -> Bool) -> SetFpt a
PropSetFpt f x = (f x = True)

public export
propSet : (f : a -> Bool) -> Set (PropSetFpt f)
propSet f x = decEq (f x) True
