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
vect : DecEq a => (xs : Vect k a) -> Set a
vect xs = MkSet (\x => Elem x xs) (\x => isElem x xs)
