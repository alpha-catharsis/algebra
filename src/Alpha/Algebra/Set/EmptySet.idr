---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.EmptySet

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.BasicOps
import Alpha.Algebra.Set.Set

------------
-- Empty set
------------

EmptySetPrf : SetFpt a
EmptySetPrf = const Void

export
emptySet : SetFn EmptySetPrf
emptySet _ = No uninhabited

export
Uninhabited (SetPrf (IntersectionPrf EmptySetPrf rfpt) x) where
  uninhabited (_,_) impossible

export
Uninhabited (SetPrf (IntersectionPrf lfpt EmptySetPrf) x) where
  uninhabited (_,_) impossible

----------------------
-- Empty set relations
----------------------

-- subsetEmptySet : (rs : Set a) -> Subset (EmptySet.emptySet, rs)
-- subsetEmptySet ls = MkSubset (emptySet, ls) (\prf => absurd (uninhabited prf))
