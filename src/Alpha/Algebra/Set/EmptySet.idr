---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.EmptySet

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Relation.Relation
import Alpha.Algebra.Relation.Set
import Alpha.Algebra.Set.BasicOps
import Alpha.Algebra.Set.Set

------------
-- Empty set
------------

public export
EmptySet : Set a
EmptySet _ = Void

export
emptySet : SetDec EmptySet
emptySet _ = No uninhabited

export
Uninhabited (Elem x EmptySet) where
  uninhabited _ impossible

export
Uninhabited (Elem x (Intersection EmptySet rs)) where
  uninhabited (_,_) impossible

export
Uninhabited (Elem x (Intersection ls EmptySet)) where
  uninhabited (_,_) impossible

export
subsetEmptySet : Related (EmptySet, rs) Subset
subsetEmptySet = absurd
