---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Inclusion

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Relation
import Alpha.Algebra.Set.Set

---------------------
-- Inclusion relation
---------------------

public export
data Inclusion = MkInclusion

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
isSubset : (Set t a, Set u a, Relation Inclusion t u) =>
           (ls : t) -> (rs : u) -> Dec (RelationPrf MkInclusion ls rs)
isSubset ls rs = areRelated MkInclusion ls rs

export
subset : (Set t a, Set u a, Relation Inclusion t u) =>
         (ls : t) -> (rs : u) -> Bool
subset ls rs = related MkInclusion ls rs

--------------------------------
-- Inclusion relation properties
--------------------------------

-- (Set t a, Relation Inclusion t t) => RelationRefl Inclusion t where
--   reflRelation r s = (\_ => MkSubset s s id)

-- export
-- (Set t a) => Includable t UniverseSet a where
--   isSubset ls MkUniverseSet = Yes (MkSubset ls MkUniverseSet
--                                    (\_ => MkElemUniverseSet))

-- export
-- (Set u a) => Includable EmptySet u a where
--   isSubset MkEmptySet rs = Yes (MkSubset MkEmptySet rs
--                                 (\prf => absurd (uninhabited prf)))

-- subset : (Includable t u a) => t -> u -> Bool
-- subset ls rs = isYes (isSubset {a} ls rs)

-- (Includable t u a) => Relation Inclusion UniverseSet UniverseSet t u where
--   RelationPrf = Subset
--   areRelated _ _ _ ls rs _ _ = isSubset ls rs

-- (Includable t u a) => RelationRefl Inclusion UniverseSet UniverseSet where



-- export
-- inclusionReflexive : (s : Set a) -> Subset s s
-- inclusionReflexive s = MkSubset s s id

-- export
-- inclusionTransitive : (ls : Set a) -> (ms : Set a) -> (rs : Set a) ->
--                       Subset ls ms -> Subset ms rs -> Subset ls rs
-- inclusionTransitive ls ms rs (MkSubset ls ms lprf) (MkSubset ms rs rprf) =
--   MkSubset ls rs (rprf . lprf)

-- export
-- inclusionAntiSymmetric : (ls : Set a) -> (rs : Set a) ->
--                          Subset ls rs -> Subset rs ls -> EqualSet ls rs
-- inclusionAntiSymmetric ls rs (MkSubset ls rs prf) (MkSubset rs ls rprf) =
--   MkEqualSet ls rs prf rprf
