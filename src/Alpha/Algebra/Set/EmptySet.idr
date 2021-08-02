---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.EmptySet

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Relation
import Alpha.Algebra.Set.Inclusion
import Alpha.Algebra.Set.Set

------------
-- Empty set
------------

public export
data EmptySet : Type -> Type where
 MkEmptySet : (a : Type) -> EmptySet a

public export
data ElemEmptySet : (x : a) -> (s : EmptySet a) -> Type where

export
Uninhabited (ElemEmptySet x s) where
  uninhabited _ impossible

public export
Set (EmptySet a) a where
  SetElemPrf = ElemEmptySet
  isElem _ _ = No uninhabited

export
(Set u a) => Relation (EmptySet a) u Subset where
  areRelated (MkEmptySet a) rs =  Yes (MkSubset (MkEmptySet a) rs
                                       (\prf => absurd (uninhabited prf)))





-- export
-- Uninhabited (Elem x EmptySet.emptySet) where
--   uninhabited (MkElem _ _ _) impossible

-- export
-- Uninhabited (Elem x (intersection EmptySet.emptySet rs)) where
--   uninhabited (MkElem _ _ (_, _)) impossible

-- export
-- Uninhabited (Elem x (intersection ls EmptySet.emptySet)) where
--   uninhabited (MkElem _ _ (_, _)) impossible
