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

UniverseSetPrf : SetFpt a
UniverseSetPrf = const ()

export
universeSet : SetFn UniverseSetPrf
universeSet _ = Yes ()

export
Uninhabited (SetPrf (ComplementPrf UniverseSetPrf) x) where
  uninhabited contra = contra ()


-- export
-- elemUnionUniverseLeft : {x : a} -> {rs : Set a} ->
--                         Elem x (union UniverseSet.universeSet rs)
-- elemUnionUniverseLeft = MkElem _ _ (Left ())

-- export
-- elemUnionUniverseRight : {x : a} -> {ls : Set a} ->
--                          Elem x (union ls UniverseSet.universeSet)
-- elemUnionUniverseRight = MkElem _ _ (Right ())
