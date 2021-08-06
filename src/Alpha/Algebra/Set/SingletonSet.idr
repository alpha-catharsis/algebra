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

-- import Alpha.Algebra.Set.PointedSet
import Alpha.Algebra.Set.Set

----------------
-- Singleton set
----------------

public export
SingletonSet : (v : a) -> Set a
SingletonSet v x = (x = v)

public export
singletonSet : DecEq a => (v : a) -> SetDec (SingletonSet v)
singletonSet v x = decEq x v

