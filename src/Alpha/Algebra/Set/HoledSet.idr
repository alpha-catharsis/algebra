---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.HoledSet

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Function.NullryFn
import Alpha.Algebra.Set.PointedSet
import Alpha.Algebra.Set.Set
import Alpha.Decidable

------------
-- Holed set
------------

public export
HoledSet : (v : a) -> Set a
HoledSet v x = (x = v) -> Void

public export
holedSet : DecEq a => (v : a) -> SetDec (HoledSet v)
holedSet v x = decNot (decEq x v)

data Negg : {a : Type} -> (x : a) -> (y : a) -> Type where
  MkNegg : (x = y -> Void) -> Negg x y

export
HoledPointedSet : {a : Type} -> DecEq a => {v : a} -> SetDec (HoledSet v) ->
                  (x : a) -> (x = v -> Void) -> PointedSet (HoledSet v)
HoledPointedSet sd x prf = pointedSet sd (nullryFn (HoledSet v) x {prf})
