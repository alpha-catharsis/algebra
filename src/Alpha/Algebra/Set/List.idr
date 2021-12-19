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
0 ListSet : List a -> Set a
ListSet xs x = List.Elem.Elem x xs

public export
list : DecEq a => (xs : List a) -> DecSet (ListSet xs)
list xs x = List.Elem.isElem x xs
