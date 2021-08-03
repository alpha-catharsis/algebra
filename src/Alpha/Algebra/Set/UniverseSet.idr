---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.UniverseSet

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.BasicOps
import Alpha.Decidable

---------------
-- Universe set
---------------

export
universeSet : Set a
universeSet = MkSet (const ()) (const (Yes ()))

export
elemUniverse : {x : a} -> Elem x UniverseSet.universeSet
elemUniverse = MkElem _ _ ()

export
Uninhabited (Elem x (complement UniverseSet.universeSet)) where
  uninhabited (MkElem _ _ contra) = contra ()

export
elemUnionUniverseLeft : {x : a} -> {rs : Set a} ->
                        Elem x (union UniverseSet.universeSet rs)
elemUnionUniverseLeft = MkElem _ _ (Left ())

export
elemUnionUniverseRight : {x : a} -> {ls : Set a} ->
                         Elem x (union ls UniverseSet.universeSet)
elemUnionUniverseRight = MkElem _ _ (Right ())

