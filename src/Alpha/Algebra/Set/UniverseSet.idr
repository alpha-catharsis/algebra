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
UniverseSet : Set a
UniverseSet _ = ()

export
universeSet : SetDec UniverseSet
universeSet _ = Yes ()

export
Uninhabited (Elem x (Complement UniverseSet)) where
  uninhabited contra = contra ()

export
elemUniverseSet : Elem x UniverseSet
elemUniverseSet = ()

export
elemUnionUniverseSetLeft : Elem x (Union UniverseSet _)
elemUnionUniverseSetLeft = Left ()

export
elemUnionUniverseSetRight : Elem x (Union _ UniverseSet)
elemUnionUniverseSetRight = Right ()

export
subsetUniverseSet : Related (ls, UniverseSet) Subset
subsetUniverseSet _ = ()
