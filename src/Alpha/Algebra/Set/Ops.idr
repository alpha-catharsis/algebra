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
compl : Set a -> Set a
compl s = MkSet (\x => SetContra s x) (\x => decNot (setDec s x))

---------------
-- Intersection
---------------

public export
inter : Set a -> Set a -> Set a
inter ls rs = MkSet (\x => (SetPrf ls x, SetPrf rs x))
              (\x => decAnd (setDec ls x) (setDec rs x))

--------
-- Union
--------

public export
union : Set a -> Set a -> Set a
union ls rs = MkSet (\x => Either (SetPrf ls x) (SetPrf rs x))
              (\x => decOr (setDec ls x) (setDec rs x))

-------------
-- Difference
-------------

public export
diff : Set a -> Set a -> Set a
diff ls rs = inter ls (compl rs)

-----------------------
-- Symmetric difference
-----------------------

public export
symmDiff : Set a -> Set a -> Set a
symmDiff ls rs = union (diff ls rs) (diff rs ls)
