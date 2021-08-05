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

EmptySetFpt : SetFpt a
EmptySetFpt _ = Void

export
emptySet : Set EmptySetFpt
emptySet _ = No uninhabited

export
Uninhabited (Elem x (IntersectionFpt EmptySetFpt rfpt)) where
  uninhabited (_,_) impossible

export
Uninhabited (Elem x (IntersectionFpt lfpt EmptySetFpt)) where
  uninhabited (_,_) impossible

----------------------
-- Empty set relations
----------------------

-- subsetEmptySet : (rs : Set a) -> Subset (EmptySet.emptySet, rs)
-- subsetEmptySet ls = MkSubset (emptySet, ls) (\prf => absurd (uninhabited prf))
