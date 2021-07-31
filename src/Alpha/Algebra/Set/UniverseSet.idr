---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.UniverseSet

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Inclusion
import Alpha.Algebra.Set.Set
-- import Alpha.Algebra.Set.BasicOps
-- import Alpha.Decidable

---------------
-- Universe set
---------------

public export
data UniverseSet : Type where
  MkUniverseSet : UniverseSet

public export
data ElemUniverseSet : (x : a) -> (s : UniverseSet) -> Type where
  MkElemUniverseSet : ElemUniverseSet x MkUniverseSet

export
Set UniverseSet a where
  SetElemPrf = ElemUniverseSet
  isElem x MkUniverseSet = Yes MkElemUniverseSet

export
subsetUniverseSet : (Set t a) => (ls : t) -> Subset ls MkUniverseSet
subsetUniverseSet ls = MkSubset ls MkUniverseSet (\_ => MkElemUniverseSet)

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
