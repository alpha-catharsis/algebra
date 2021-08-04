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
SingletonSetPrf : (v : a) -> SetFpt a
SingletonSetPrf v x = (x = v)

public export
singletonSet : DecEq a => (v : a) -> SetFn (SingletonSetPrf v)
singletonSet v x = decEq x v
