---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Relation
import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.Subset

--------------------
-- Included data type
---------------------

public export
data EqualSet : (Set t a, Set u a) => (ls : t) -> (rs : u) -> Type where
  MkEqualSet : (Set t a, Set u a) => {ls : t} -> {rs : u} ->
               Subset ls rs -> Subset rs ls ->
               EqualSet ls rs

export
notEqualSetLeft : (Set t a, Set u a) => {ls : t} -> {rs : u} ->
                  (Subset ls rs -> Void) -> Subset rs ls ->
                  EqualSet ls rs -> Void
notEqualSetLeft lcontra _ (MkEqualSet lprf _) = lcontra lprf

export
notEqualSetRight : (Set t a, Set u a) => {ls : t} -> {rs : u} ->
                   Subset ls rs -> (Subset rs ls -> Void) ->
                   EqualSet ls rs -> Void
notEqualSetRight _ rcontra (MkEqualSet _ rprf) = rcontra rprf

export
isSetEqual : (Set t a, Set u a) => (Relation t u EqualSet) =>
             (ls : t) -> (rs : u) -> Dec (EqualSet ls rs)
isSetEqual ls rs = areRelated ls rs

export
setEqual : (Set t a, Set u a) => (Relation t u EqualSet) =>
           (ls : t) -> (rs : u) -> Bool
setEqual ls rs = related EqualSet ls rs

export
(Set t a) => (Relation t t Subset, Relation t t EqualSet) =>
RelationRefl t EqualSet where
  reflRelation = MkEqualSet (reflRelation {a=t} {r=Subset})
                            (reflRelation {a=t} {r=Subset})

export
(Set t a) => (Relation t t EqualSet) =>
RelationSymm t EqualSet  where
  symmRelation (MkEqualSet fprf bprf) = MkEqualSet bprf fprf

export
(Set t a) => (Relation t t Subset, Relation t t EqualSet) =>
 RelationTrans t EqualSet  where
  transRelation (MkEqualSet lfprf lbprf) (MkEqualSet rfprf rbprf) =
    MkEqualSet (transRelation lfprf rfprf {a=t} {r=Subset})
               (transRelation rbprf lbprf {a=t} {r=Subset})



