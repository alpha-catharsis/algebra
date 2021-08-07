---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.EmptySet

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Relation.Relation
import Alpha.Algebra.Relation.Set
import Alpha.Algebra.Set.BasicOps
import Alpha.Algebra.Set.Set

------------
-- Empty set
------------

public export
EmptySet : Set a
EmptySet _ = Void

export
emptySet : SetDec EmptySet
emptySet _ = No uninhabited

export
Uninhabited (Elem x EmptySet) where
  uninhabited _ impossible

export
Uninhabited (Elem x (Intersection EmptySet rs)) where
  uninhabited (_,_) impossible

export
Uninhabited (Elem x (Intersection ls EmptySet)) where
  uninhabited (_,_) impossible

export
subsetEmptySet : Related (EmptySet, rs) Subset
subsetEmptySet = absurd

export
neutralEmptyUnionLeft : {s : Set a} -> Related (s, Union EmptySet s) EqualSets
neutralEmptyUnionLeft = (Right, \ef => case ef of
                                         Left f => absurd (uninhabited f)
                                         Right f => f)

export
neutralEmptyUnionRight : {s : Set a} -> Related (s, Union s EmptySet) EqualSets
neutralEmptyUnionRight = (Left, \ef => case ef of
                                         Left f => f
                                         Right f => absurd (uninhabited f))

export
absorbEmptyIntersectionLeft : {s : Set a} ->
   Related (EmptySet, Intersection EmptySet s) EqualSets
absorbEmptyIntersectionLeft = (\lprf => (lprf, absurd (uninhabited lprf)),
                                         fst)

export
absorbEmptyIntersectionRight : {s : Set a} ->
  Related (EmptySet, Intersection s EmptySet) EqualSets
absorbEmptyIntersectionRight = (\rprf => (absurd (uninhabited rprf), rprf),
                                          snd)
