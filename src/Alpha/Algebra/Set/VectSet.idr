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

import Alpha.Algebra.Function.NullryFn
import Alpha.Algebra.Set.PointedSet
import Alpha.Algebra.Set.Set

-----------
-- Vect set
-----------

public export
VectSet : Vect k a -> Set a
VectSet xs x = VE.Elem x xs

public export
vectSet : DecEq a => (xs : Vect k a) -> SetDec (VectSet xs)
vectSet xs x = VE.isElem x xs

export
vectPointedSet : {xs : Vect k a} -> SetDec (VectSet xs) -> (x : a) ->
                {auto prf : VE.Elem x xs} -> PointedSet (VectSet xs)
vectPointedSet sd x = (sd, (x ** prf))
