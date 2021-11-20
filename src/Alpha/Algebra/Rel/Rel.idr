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
-- 0 RelPrfTy : Type -> Type -> Type
-- RelPrfTy a b = SetPrfTy (a,b)

-- public export
-- 0 Rel : RelPrfTy a b -> Type
-- Rel pf = (p : (a,b)) -> Dec (pf p)

-- public export
-- areRelated : (x : a) -> (y : b) -> (r : Rel pty) -> Dec (pty (x,y))
-- areRelated x y r = r (x,y)

-- public export
-- related : (x : a) -> (y : b) -> {pty : RelPrfTy a b} -> (r : Rel pty) -> Bool
-- related x y r = isYes (areRelated x y r)

----------------------
-- Relation properties
----------------------

-- public export
-- 0 RelRefl : RelPrfTy a a -> Type
-- RelRefl pty = {x : a} -> pty (x,x)

-- public export
-- 0 RelTrans : RelPrfTy a a -> Type
-- RelTrans pty = {x : a} -> {y : a} -> {z : a} ->
--                pty (x,y) -> pty (y,z) -> pty (x,z)


-- public export
-- 0 RelAsymm : RelPrfTy a a -> RelPrfTy a a -> Type
-- RelAsymm pty epty = {x : a} -> {y : a} -> pty (x,y) -> pty (y,x) -> epty (x,y)
