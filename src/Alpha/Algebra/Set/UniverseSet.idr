---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.UniverseSet

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.BasicOps
import Alpha.Algebra.Set.Set

---------------
-- Universe set
---------------

UniverseSetFpt : SetFpt a
UniverseSetFpt _ = ()

export
universeSet : Set UniverseSetFpt
universeSet _ = Yes ()

export
Uninhabited (Elem x (ComplementFpt UniverseSetFpt)) where
  uninhabited contra = contra ()


-- export
-- elemUnionUniverseLeft : {x : a} -> {rs : Set a} ->
--                         Elem x (union UniverseSet.universeSet rs)
-- elemUnionUniverseLeft = MkElem _ _ (Left ())

-- export
-- elemUnionUniverseRight : {x : a} -> {ls : Set a} ->
--                          Elem x (union ls UniverseSet.universeSet)
-- elemUnionUniverseRight = MkElem _ _ (Right ())
