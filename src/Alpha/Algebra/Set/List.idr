---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.List

-------------------
-- External imports
-------------------

import Data.DPair
import Data.List.Elem
import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

-----------
-- List set
-----------

public export
list : DecEq a => (xs : List a) -> Set a
list xs = MkSet (\x => Elem x xs) (\x => isElem x xs)
