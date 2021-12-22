---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Ops.Union

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

--------
-- Union
--------

public export
Union : Set a -> Set a -> Set a
Union ls rs x = Either (ls x) (rs x)

public export
union : DecSet ls -> DecSet rs -> DecSet (Union ls rs)
union ls rs x = decOr (isElem x ls) (isElem x rs)
