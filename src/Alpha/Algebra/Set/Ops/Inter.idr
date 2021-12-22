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

import Alpha.Algebra.Set.Ops.Compl
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
Uninhabited (t, t -> Void) where
  uninhabited (prf,contra) = contra prf

public export
Uninhabited (t -> Void, t) where
  uninhabited (contra, prf) = contra prf
