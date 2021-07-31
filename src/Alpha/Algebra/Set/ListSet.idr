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
DecEq a => Set (List a) a where
  SetElemPrf = LE.Elem
  isElem = LE.isElem
