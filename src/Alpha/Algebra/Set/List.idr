---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.List

-------------------
-- External imports
-------------------

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
0 ListPrfTy : List a -> SetPrfTy a
ListPrfTy xs x = Elem x xs

public export
list : DecEq a => (xs : List a) -> Set (ListPrfTy xs)
list xs x = isElem x xs
