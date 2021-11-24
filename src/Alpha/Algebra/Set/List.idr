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
0 ListPty : List a -> SetPty a
ListPty xs x = Elem x xs

public export
list : DecEq a => (xs : List a) -> Set (ListPty xs)
list xs x = isElem x xs
