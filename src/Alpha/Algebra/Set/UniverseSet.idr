---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.UniverseSet

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Relation
import Alpha.Algebra.Set.BasicOps
import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.Subset

---------------
-- Universe set
---------------

public export
UniverseSetFpt : SetFpt a
UniverseSetFpt _ = ()

export
universeSet : Set UniverseSetFpt
universeSet _ = Yes ()

export
Uninhabited (Elem x (ComplementFpt UniverseSetFpt)) where
  uninhabited contra = contra ()

export
elemUniverseSet : Elem x UniverseSetFpt
elemUniverseSet = ()

export
elemUnionUniverseSetLeft : Elem x (UnionFpt UniverseSetFpt _)
elemUnionUniverseSetLeft = Left ()

export
elemUnionUniverseSetRight : Elem x (UnionFpt _ UniverseSetFpt)
elemUnionUniverseSetRight = Right ()

export
subsetUniverseSet : Related (ls, UniverseSet.universeSet) Subset
subsetUniverseSet _ = ()
