---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Prop

-------------------
-- External imports
-------------------

import Data.DPair
import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

------------------
-- Proposition Set
------------------

public export
PropPrf : (f : a -> Bool) -> SetPty a
PropPrf f x = f x = True

public export
prop : (f : a -> Bool) -> Set (PropPrf f)
prop f x = decEq (f x) True
