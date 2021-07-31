---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.EmptySet

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Inclusion
import Alpha.Algebra.Set.Set
-- import Alpha.Algebra.Set.BasicOps

------------
-- Empty set
------------

public export
data EmptySet : Type where
 MkEmptySet : EmptySet

public export
data ElemEmptySet : (x : a) -> (s : EmptySet) -> Type where

export
Uninhabited (ElemEmptySet x s) where
  uninhabited _ impossible

export
Set EmptySet a where
  SetElemPrf = ElemEmptySet
  isElem _ _ = No uninhabited

export
notSubsetEmptySet : (Set t a) => (ls : t) -> (x : a) -> SetElemPrf x ls ->
                    Subset ls MkEmptySet -> Void
notSubsetEmptySet ls x prf = notSubset ls MkEmptySet x prf uninhabited


-- export
-- Uninhabited (Elem x EmptySet.emptySet) where
--   uninhabited (MkElem _ _ _) impossible

-- export
-- Uninhabited (Elem x (intersection EmptySet.emptySet rs)) where
--   uninhabited (MkElem _ _ (_, _)) impossible

-- export
-- Uninhabited (Elem x (intersection ls EmptySet.emptySet)) where
--   uninhabited (MkElem _ _ (_, _)) impossible
