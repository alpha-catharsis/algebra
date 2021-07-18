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

import Alpha.Algebra.Set.Set
import Alpha.Decidable

------------
-- Holed set
------------

export
holed : DecEq a => (x : a) -> Set a
holed x = MkSet (\y => Not (x = y)) (\y => decNot (decEq x y))

export
{x : a} -> DecEq a => Uninhabited (Elem x (holed x)) where
  uninhabited (MkElem _ _ contra) = contra Refl

export
elemHoled : DecEq a => {y : a} -> {x : a} -> {auto contra : Not (x = y)} ->
            Elem y (holed x)
elemHoled = MkElem _ _ contra
