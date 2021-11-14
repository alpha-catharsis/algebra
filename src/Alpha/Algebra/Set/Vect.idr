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
0 VectPrfTy : Vect k a -> SetPrfTy a
VectPrfTy xs x = Elem x xs

public export
vect : DecEq a => (xs : Vect k a) -> Set (VectPrfTy xs)
vect xs x = isElem x xs
