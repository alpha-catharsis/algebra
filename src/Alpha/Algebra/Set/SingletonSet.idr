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
SingletonSetFpt : (v : a) -> SetFpt a
SingletonSetFpt v x = (x = v)

public export
singletonSet : DecEq a => (v : a) -> Set (SingletonSetFpt v)
singletonSet v x = decEq x v
