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
compl s = (\x => fst s x -> Void ** \x => decNot (snd s x))

---------------
-- Intersection
---------------

public export
inter : Set a -> Set a -> Set a
inter s s' = (\x => (fst s x, fst s' x) ** \x => decAnd (snd s x) (snd s' x))

--------
-- Union
--------

public export
union : Set a -> Set a -> Set a
union s s' = (\x => Either (fst s x) (fst s' x) ** \x => decOr (snd s x) (snd s' x))

-------------
-- Difference
-------------

public export
diff : Set a -> Set a -> Set a
diff s s' = inter s (compl s')

-----------------------
-- Symmetric difference
-----------------------

public export
symmDiff : Set a -> Set a -> Set a
symmDiff s s' = union (diff s s') (diff s' s)
