---------------------
 -- Module declaration
---------------------

module Alpha.Algebra.Set.ListSet

-------------------
-- External imports
-------------------

import Data.List.Elem as LE

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

-----------
-- List set
-----------

public export
ListSetPrf : List a -> SetFpt a
ListSetPrf xs x = LE.Elem x xs

public export
listSet : DecEq a => (xs : List a) -> SetFn (ListSetPrf xs)
listSet xs x = LE.isElem x xs

