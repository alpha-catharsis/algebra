---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.VectSet

-------------------
-- External imports
-------------------

import Data.Vect.Elem as VE

import Data.Vect
import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

-----------
-- Vect set
-----------

export
DecEq a => Set (Vect k a) a where
  SetElemPrf = VE.Elem
  isElem = VE.isElem
