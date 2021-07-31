---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.UniverseSet

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
-- import Alpha.Algebra.Set.BasicOps
-- import Alpha.Decidable

---------------
-- Universe set
---------------

public export
data UniverseSet : Type -> Type where
  MkUniverseSet : (a : Type) -> UniverseSet a

public export
data ElemUniverseSet : (x : a) -> (s : t) -> Type where
  MkElemUniverseSet : ElemUniverseSet x s

export
Set (UniverseSet a) a where
  SetElemPrf = ElemUniverseSet
  isElem _ _ = Yes (MkElemUniverseSet)


-- export
-- Uninhabited (Elem x (complement UniverseSet.universeSet)) where
--   uninhabited (MkElem _ _ contra) = contra ()

-- export
-- elemUnionUniverseLeft : {x : a} -> {rs : Set a} ->
--                         Elem x (union UniverseSet.universeSet rs)
-- elemUnionUniverseLeft = MkElem _ _ (Left ())

-- export
-- elemUnionUniverseRight : {x : a} -> {ls : Set a} ->
--                          Elem x (union ls UniverseSet.universeSet)
-- elemUnionUniverseRight = MkElem _ _ (Right ())
