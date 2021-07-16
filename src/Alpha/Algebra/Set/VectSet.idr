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
vectSet : DecEq a => (xs : Vect k a) -> Set (\x => VE.Elem x xs) a
vectSet xs = MkSet (\x => VE.isElem x xs)
