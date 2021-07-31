---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Inclusion

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.Sets
import Alpha.Algebra.Set.ProductOps
import Alpha.Algebra.Relation
import Alpha.Algebra.Set.UniverseSet

---------------------
-- Subset data type
---------------------

-- public export
-- data Subset : Type -> Type -> Type where
--   MkSubset : (Set t a, Set u a) => (ls : t) -> (rs : u) ->
--              (prf : {x : a} -> SetElemPrf x ls -> SetElemPrf x rs) ->
--              Subset t u

data Inclusion = MkInclusion

data Subset : (_ : Inclusion) -> (_ : UniverseSet t) -> (_ : UniverseSet u) ->
              (ls : t) -> (rs : u) -> Type where
  MkSubset : (Set t a, Set u a) => (ls : t) -> (rs : u) ->
             (prf : {x : a} -> SetElemPrf x ls -> SetElemPrf x rs) ->
             Subset MkInclusion (MkUniverseSet t) (MkUniverseSet u) ls rs

-- Relation Inclusion (UniverseSet (UniverseSet a)) (UniverseSet (UniverseSet a))
--          (UniverseSet a) (UniverseSet a) where
--   RelationPrf = Subset
--   areRelated _ _ _ ls rs = MkSubset ls rs (\_,prf => prf)

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
