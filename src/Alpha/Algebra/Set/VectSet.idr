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
vectSet : DecEq a => (xs : Vect k a) -> Set a
vectSet xs = MkSet (\x => VE.Elem x xs) (\x => VE.isElem x xs)
