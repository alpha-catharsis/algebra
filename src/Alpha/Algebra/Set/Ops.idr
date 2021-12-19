---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Ops

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
import Alpha.Decidable

-------------
-- Complement
-------------

public export
Compl : Set a -> Set a
Compl s = Not . s

public export
compl : DecSet s -> DecSet (Compl s)
compl s x = decNot (isElem x s)

---------------
-- Intersection
---------------

public export
Inter : Set a -> Set a -> Set a
Inter ls rs x = (ls x, rs x)

public export
inter : DecSet ls -> DecSet rs -> DecSet (Inter ls rs)
inter ls rs x = decAnd (isElem x ls) (isElem x rs)

--------
-- Union
--------

public export
Union : Set a -> Set a -> Set a
Union ls rs x = Either (ls x) (rs x)

public export
union : DecSet ls -> DecSet rs -> DecSet (Union ls rs)
union ls rs x = decOr (isElem x ls) (isElem x rs)

-------------
-- Difference
-------------

public export
Diff : Set a -> Set a -> Set a
Diff ls rs = Inter ls (Compl rs)

public export
diff : DecSet ls -> DecSet rs -> DecSet (Diff ls rs)
diff ls rs = inter ls (compl rs)

-----------------------
-- Symmetric difference
-----------------------

public export
SymmDiff : Set a -> Set a -> Set a
SymmDiff ls rs = Union (Diff ls rs) (Diff rs ls)

public export
symmDiff : DecSet ls -> DecSet rs -> DecSet (SymmDiff ls rs)
symmDiff ls rs = union (diff ls rs) (diff rs ls)
