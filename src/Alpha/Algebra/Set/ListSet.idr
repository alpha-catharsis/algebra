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

export
listSet : DecEq a => (xs : List a) -> Set a
listSet xs = MkSet (\x => LE.Elem x xs) (\x => LE.isElem x xs)
