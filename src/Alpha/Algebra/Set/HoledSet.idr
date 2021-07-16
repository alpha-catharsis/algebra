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

public export
holed : DecEq a => (x : a) -> Set (\y => Not (x = y)) a
holed x = MkSet (\y => decNot (decEq x y))

public export
{x : a} -> DecEq a => Uninhabited (Elem x (holed x)) where
  uninhabited (MkElem _ _ contra) = contra Refl

public export
elemHoled : DecEq a => {y : a} -> {x : a} -> {auto contra : Not (x = y)} ->
            Elem y (holed x)
elemHoled = MkElem _ _ contra
