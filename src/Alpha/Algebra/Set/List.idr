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
0 ListPrf : List a -> SetPrfTy a
ListPrf xs x = Elem x xs

public export
Set (List a) a where
  SetPrf = ListPrf

public export
DecEq a => DecSet (List a) a where
  isElem = List.Elem.isElem
