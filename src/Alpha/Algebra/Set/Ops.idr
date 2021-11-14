---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Ops

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
import Alpha.Decidable

-------------
-- Complement
-------------

public export
0 ComplPrfTy : SetPrfTy a -> SetPrfTy a
ComplPrfTy pf x = pf x -> Void

public export
compl : Set pty -> Set (ComplPrfTy pty)
compl s x = decNot (s x)

---------------
-- Intersection
---------------

public export
0 InterPrfTy : SetPrfTy a -> SetPrfTy a -> SetPrfTy a
InterPrfTy lpf rpf x = (lpf x, rpf x)

public export
inter : Set lpty -> Set rpty -> Set (InterPrfTy lpty rpty)
inter ls rs x = decAnd (ls x) (rs x)

--------
-- Union
--------

public export
0 UnionPrfTy : SetPrfTy a -> SetPrfTy a -> SetPrfTy a
UnionPrfTy lpf rpf x = Either (lpf x) (rpf x)

public export
union : Set lpty -> Set rpty -> Set (UnionPrfTy lpty rpty)
union ls rs x = decOr (ls x) (rs x)

-------------
-- Difference
-------------

public export
0 DiffPrfTy : SetPrfTy a -> SetPrfTy a -> SetPrfTy a
DiffPrfTy lpf rpf = InterPrfTy lpf (ComplPrfTy rpf)

public export
diff : Set lpty -> Set rpty -> Set (DiffPrfTy lpty rpty)
diff ls rs = inter ls (compl rs)

-----------------------
-- Symmetric difference
-----------------------

public export
0 SymmDiffPrfTy : SetPrfTy a -> SetPrfTy a -> SetPrfTy a
SymmDiffPrfTy lpf rpf = UnionPrfTy (DiffPrfTy lpf rpf) (DiffPrfTy rpf lpf)

public export
symmDiff : Set lpty -> Set rpty -> Set (SymmDiffPrfTy lpty rpty)
symmDiff ls rs = union (diff ls rs) (diff rs ls)
