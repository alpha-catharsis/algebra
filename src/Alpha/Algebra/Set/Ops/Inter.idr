---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Ops.Inter

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.Empty
import Alpha.Decidable

---------------
-- Intersection
---------------

public export
Inter : Set a -> Set a -> Set a
Inter ls rs x = (ls x, rs x)

public export
inter : DecSet ls -> DecSet rs -> DecSet (Inter ls rs)
inter ls rs x = decAnd (isElem x ls) (isElem x rs)

public export
Uninhabited (Inter EmptySet rs x) where
  uninhabited (lprf,_) = lprf ()

public export
Uninhabited (Inter ls EmptySet x) where
  uninhabited (_,rprf) = rprf ()
