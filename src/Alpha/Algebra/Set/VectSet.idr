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

public export
VectSetFpt : Vect k a -> SetFpt a
VectSetFpt xs x = VE.Elem x xs

public export
vectSet : DecEq a => (xs : Vect k a) -> Set (VectSetFpt xs)
vectSet xs x = VE.isElem x xs
