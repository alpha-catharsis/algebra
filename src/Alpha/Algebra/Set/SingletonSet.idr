---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.SingletonSet

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

----------------
-- Singleton set
----------------

public export
singleton : DecEq a => (x : a) -> Set (\y => x = y) a
singleton x = MkSet (\y => decEq x y)

public export
elemSingleton : DecEq a => {x : a} -> Elem x (singleton x)
elemSingleton = MkElem _ _ Refl

public export
notElemSingleton : DecEq a => {y : a} -> {auto contra : (x = y) -> Void} -> Elem y (singleton x) -> Void
notElemSingleton (MkElem _ _ prf) = contra prf
