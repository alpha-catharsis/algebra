---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Vect

-------------------
-- External imports
-------------------

import Data.Vect
import Data.Vect.Elem
import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

-----------
-- List set
-----------

public export
0 VectPrf : Vect k a -> SetPrfTy a
VectPrf xs x = Elem x xs

public export
Set (Vect k a) a where
  SetPrf = VectPrf

public export
DecEq a => DecSet (Vect k a) a where
  isElem = Vect.Elem.isElem
