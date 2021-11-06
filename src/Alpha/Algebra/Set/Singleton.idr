---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Singleton

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Ops
import Alpha.Algebra.Set.Pointed
import Alpha.Algebra.Set.Set

----------------
-- Singleton set
----------------

public export
singl : DecEq a => (x : a) -> Set a
singl x = (\y => y = x ** \y => decEq y x)

------------
-- Holed set
------------

public export
holed : DecEq a => (x : a) -> Set a
holed x = compl (singl x)

--------------------
-- Pointed singleton
--------------------

public export
pointedSingl : DecEq a => (x : a) -> Pointed a
pointedSingl x = (singl x ** (x ** Refl))
