---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Subset

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Relation
import Alpha.Algebra.Set.Set

-------------------
-- Subset data type
-------------------

public export
data Subset : (Set t a, Set u a) => (ls : t) -> (rs : u) -> Type where
  MkSubset : (Set t a, Set u a) => (ls : t) -> (rs : u) ->
             (prf : {x : a} -> SetElemPrf x ls -> SetElemPrf x rs) ->
             Subset ls rs

export
notSubset : (Set t a, Set u a) => (ls : t) -> (rs : u) ->
            (x : a) -> SetElemPrf x ls -> (SetElemPrf x rs -> Void) ->
            Subset ls rs -> Void
notSubset ls rs x prf contra (MkSubset ls rs f) = contra (f {x} prf)

export
elemSubset : (Set t a, Set u a) => {ls : t} -> {rs : u} -> {x : a} ->
             Subset ls rs -> SetElemPrf x ls -> SetElemPrf x rs
elemSubset (MkSubset ls rs f) prf = f prf

export
isSubset : (Set t a, Set u a) => (Relation t u Subset) =>
           (ls : t) -> (rs : u) -> Dec (Subset ls rs)
isSubset ls rs = areRelated ls rs

export
subset : (Set t a, Set u a) => (Relation t u Subset) =>
         (ls : t) -> (rs : u) -> Bool
subset ls rs = related Subset ls rs

export
(Set t a) => (Relation t t Subset) => RelationRefl t Subset where
  reflRelation = MkSubset _ _ id

export
(Set t a) => (Relation t t Subset) => RelationTrans t Subset where
  transRelation (MkSubset x y lprf) (MkSubset y z rprf) =
    MkSubset x z (rprf . lprf)



-- export
-- inclusionAntiSymmetric : (ls : Set a) -> (rs : Set a) ->
--                          Subset ls rs -> Subset rs ls -> EqualSet ls rs
-- inclusionAntiSymmetric ls rs (MkSubset ls rs prf) (MkSubset rs ls rprf) =
--   MkEqualSet ls rs prf rprf
