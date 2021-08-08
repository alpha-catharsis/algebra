---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.UniverseSet

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Function.NullryFn
import Alpha.Algebra.Relation.Relation
import Alpha.Algebra.Relation.Set
import Alpha.Algebra.Set.BasicOps
import Alpha.Algebra.Set.PointedSet
import Alpha.Algebra.Set.Set


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

export
neutralUniverseIntersectionLeft : {s : Set a} ->
  Related (s, Intersection UniverseSet s) EqualSets
neutralUniverseIntersectionLeft = (\x => ((),x), snd)

export
neutralUniverseIntersectionRight : {s : Set a} ->
  Related (s, Intersection s UniverseSet) EqualSets
neutralUniverseIntersectionRight = (\x => (x,()), fst)

export
absorbUniverseUnionLeft : {s : Set a} ->
  Related (UniverseSet, Union UniverseSet s) EqualSets
absorbUniverseUnionLeft = (Left, \_ => ())

export
absorbUniverseUnionRight : {s : Set a} ->
  Related (UniverseSet, Union s UniverseSet) EqualSets
absorbUniverseUnionRight = (Right, \_ => ())

export
UniversePointedSet : {a : Type} -> (x : a) -> PointedSet UniverseSet {a}
UniversePointedSet x = pointedSet universeSet (nullryFn UniverseSet x)
