---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.EmptySet

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
-- import Alpha.Algebra.Set.BasicOps

------------
-- Empty set
------------

public export
data EmptySet : Type -> Type where
 MkEmptySet : (a : Type) -> EmptySet a

public export
data ElemEmptySet : (x : a) -> (s : t) -> Type where

export
Uninhabited (ElemEmptySet a t) where
  uninhabited _ impossible

export
Set (EmptySet a) a where
  SetElemPrf = ElemEmptySet
  isElem _ _ = No uninhabited

-- export
-- Uninhabited (Elem x EmptySet.emptySet) where
--   uninhabited (MkElem _ _ _) impossible

-- export
-- Uninhabited (Elem x (intersection EmptySet.emptySet rs)) where
--   uninhabited (MkElem _ _ (_, _)) impossible

-- export
-- Uninhabited (Elem x (intersection ls EmptySet.emptySet)) where
--   uninhabited (MkElem _ _ (_, _)) impossible
