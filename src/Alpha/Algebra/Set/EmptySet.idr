---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.EmptySet

-------------------
-- Internal imports
-------------------

-- import Alpha.Algebra.Relation
-- import Alpha.Algebra.Set.BasicOps
import Alpha.Algebra.Set.Set
-- import Alpha.Algebra.Set.Subset

------------
-- Empty set
------------

public export
EmptySet : Set a
EmptySet _ = Void

export
emptySet : SetDec EmptySet
emptySet _ = No uninhabited

-- export
-- Uninhabited (Elem x EmptySetFpt) where
--   uninhabited _ impossible

-- export
-- Uninhabited (Elem x (IntersectionFpt EmptySetFpt rfpt)) where
--   uninhabited (_,_) impossible

-- export
-- Uninhabited (Elem x (IntersectionFpt lfpt EmptySetFpt)) where
--   uninhabited (_,_) impossible

-- subsetEmptySet : Related (EmptySet.emptySet, rs) Subset
-- subsetEmptySet = absurd
