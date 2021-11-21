---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Rel

-------------------
-- External imports
-------------------

import Decidable.Decidable

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

----------------------
-- Relation definition
----------------------

-- public export
-- record Rel {0 a : Type} {0 b : Type} (0 ls : Set a) (0 rs : Set b) where
--   constructor MkRel
--   0 RelPrf : ProvenElem ls -> ProvenElem rs -> Type
--   relDec : (px : ProvenElem ls) -> (py : ProvenElem rs) -> Dec (RelPrf px py)

-- public export
-- 0 RelContra : Rel ls rs -> ProvenElem ls -> ProvenElem rs -> Type
-- RelContra r px py = Not (RelPrf r px py)

-- public export
-- areRelated : (px : ProvenElem ls) -> (py : ProvenElem rs) -> (r : Rel ls rs) ->
--              Dec (RelPrf r px py)
-- areRelated px py r = relDec r px py

-- public export
-- related : ProvenElem ls -> ProvenElem rs -> Rel ls rs -> Bool
-- related x y r = isYes (areRelated x y r)

----------------------
-- Relation properties
----------------------

-- public export
-- record ReflRel {0 a : Type} {0 s : Set a} (r : Rel s s) where
--   constructor MkReflRel
--   0 reflPrf : (px : ProvenElem s) -> RelPrf r px px

-- -- 0 RelRefl : RelPrfTy a a -> Type
-- RelRefl pty = {x : a} -> pty (x,x)

-- public export
-- 0 RelTrans : RelPrfTy a a -> Type
-- RelTrans pty = {x : a} -> {y : a} -> {z : a} ->
--                pty (x,y) -> pty (y,z) -> pty (x,z)


-- public export
-- 0 RelAsymm : RelPrfTy a a -> RelPrfTy a a -> Type
-- RelAsymm pty epty = {x : a} -> {y : a} -> pty (x,y) -> pty (y,x) -> epty (x,y)
