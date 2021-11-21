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
0 ComplPrf : SetPrf a -> SetPrf a
ComplPrf pty = Not . pty

public export
compl : Set pty -> Set (ComplPrf pty)
compl s x = decNot (s x)

---------------
-- Intersection
---------------

public export
0 InterPrf : SetPrf a -> SetPrf a -> SetPrf a
InterPrf lpty rpty x = (lpty x, rpty x)

public export
inter : Set lpty -> Set rpty -> Set (InterPrf lpty rpty)
inter ls rs x = decAnd (ls x) (rs x)

--------
-- Union
--------

public export
0 UnionPrf : SetPrf a -> SetPrf a -> SetPrf a
UnionPrf lpty rpty x = Either (lpty x) (rpty x)

public export
union : Set lpty -> Set rpty -> Set (UnionPrf lpty rpty)
union ls rs x = decOr (ls x) (rs x)

-------------
-- Difference
-------------

public export
0 DiffPrf : SetPrf a -> SetPrf a -> SetPrf a
DiffPrf lpty rpty = InterPrf lpty (ComplPrf rpty)

public export
diff : Set lpty -> Set rpty -> Set (DiffPrf lpty rpty)
diff ls rs = inter ls (compl rs)

-----------------------
-- Symmetric difference
-----------------------

public export
0 SymmDiffPrf : SetPrf a -> SetPrf a -> SetPrf a
SymmDiffPrf lpty rpty = UnionPrf (DiffPrf lpty rpty) (DiffPrf rpty lpty)

public export
symmDiff : Set lpty -> Set rpty -> Set (SymmDiffPrf lpty rpty)
symmDiff ls rs = union (diff ls rs) (diff rs ls)
