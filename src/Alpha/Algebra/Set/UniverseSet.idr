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

public export
universe : Set (\x => const () (the a x)) a
universe = MkSet (const (Yes ()))

public export
elemUniverse : {x : a} -> Elem x UniverseSet.universe
elemUniverse = MkElem _ _ ()

public export
Uninhabited (Elem x (complement UniverseSet.universe)) where
  uninhabited (MkElem _ _ contra) = contra ()

public export
elemUnionUniverseLeft : {x : a} -> {rs : Set rfpt a} ->
                        Elem x (union UniverseSet.universe rs)
elemUnionUniverseLeft = MkElem _ _ (Left ())

public export
elemUnionUniverseRight : {x : a} -> {ls : Set rfpt a} ->
                         Elem x (union ls UniverseSet.universe)
elemUnionUniverseRight = MkElem _ _ (Right ())
