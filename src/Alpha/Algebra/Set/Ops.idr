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
0 ComplPty : SetPty a -> SetPty a
ComplPty pty = Not . pty

public export
compl : Set pty -> Set (ComplPty pty)
compl s x = decNot (s x)

---------------
-- Intersection
---------------

public export
0 InterPty : SetPty a -> SetPty a -> SetPty a
InterPty lpty rpty x = (lpty x, rpty x)

public export
inter : Set lpty -> Set rpty -> Set (InterPty lpty rpty)
inter ls rs x = decAnd (ls x) (rs x)

--------
-- Union
--------

public export
0 UnionPty : SetPty a -> SetPty a -> SetPty a
UnionPty lpty rpty x = Either (lpty x) (rpty x)

public export
union : Set lpty -> Set rpty -> Set (UnionPty lpty rpty)
union ls rs x = decOr (ls x) (rs x)

-------------
-- Difference
-------------

public export
0 DiffPty : SetPty a -> SetPty a -> SetPty a
DiffPty lpty rpty = InterPty lpty (ComplPty rpty)

public export
diff : Set lpty -> Set rpty -> Set (DiffPty lpty rpty)
diff ls rs = inter ls (compl rs)

-----------------------
-- Symmetric difference
-----------------------

public export
0 SymmDiffPty : SetPty a -> SetPty a -> SetPty a
SymmDiffPty lpty rpty = UnionPty (DiffPty lpty rpty) (DiffPty rpty lpty)

public export
symmDiff : Set lpty -> Set rpty -> Set (SymmDiffPty lpty rpty)
symmDiff ls rs = union (diff ls rs) (diff rs ls)
