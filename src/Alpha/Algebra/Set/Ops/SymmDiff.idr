---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Ops.SymmDiff

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Ops.Compl
import Alpha.Algebra.Set.Ops.Diff
import Alpha.Algebra.Set.Ops.Inter
import Alpha.Algebra.Set.Ops.Union
import Alpha.Algebra.Set.Set
import Alpha.Decidable

-----------------------
-- Symmetric difference
-----------------------

public export
SymmDiff : Set a -> Set a -> Set a
SymmDiff ls rs = Union (Diff ls rs) (Diff rs ls)

public export
symmDiff : DecSet ls -> DecSet rs -> DecSet (SymmDiff ls rs)
symmDiff ls rs = union (diff ls rs) (diff rs ls)
