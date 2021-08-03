---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.UniverseSet

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Relation
import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.Subset

---------------
-- Universe set
---------------

public export
data UniverseSet : Type -> Type where
  MkUniverseSet : (a : Type) -> UniverseSet a

public export
data ElemUniverseSet : (x : a) -> (s : UniverseSet a) -> Type where
  MkElemUniverseSet : ElemUniverseSet x (MkUniverseSet a)

export
Set (UniverseSet a) a where
  SetElemPrf = ElemUniverseSet
  isElem x (MkUniverseSet a) = Yes MkElemUniverseSet

export
(Set t a) => Relation t (UniverseSet a) Subset where
  areRelated ls (MkUniverseSet a) =  Yes (MkSubset ls (MkUniverseSet a)
                                          (\_ => MkElemUniverseSet))




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
