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
PropSet : (a -> Bool) -> Set a
PropSet f x = f x = True

public export
prop : (f : a -> Bool) -> DecSet (PropSet f)
prop f x = decEq (f x) True
