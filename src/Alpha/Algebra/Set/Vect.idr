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
0 VectSet : Vect k a -> Set a
VectSet xs x = Vect.Elem.Elem x xs

public export
vect : DecEq a => (xs : Vect k a) -> DecSet (VectSet xs)
vect xs x = Vect.Elem.isElem x xs
