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

public export
0 RelPrfTy : Type -> Type -> Type
RelPrfTy a b = SetPrfTy (a,b)

public export
Rel : {a : Type} -> {b : Type} -> RelPrfTy a b -> Type
Rel pf = (p : (a,b)) -> Dec (pf p)

public export
areRelated : (x : a) -> (y : b) -> (r : Rel pty) -> Dec (pty (x,y))
areRelated x y r = r (x,y)

public export
related : (x : a) -> (y : b) -> {pty : RelPrfTy a b} -> (r : Rel pty) -> Bool
related x y r = isYes (areRelated x y r)

----------------------
-- Relation properties
----------------------

-- public export
-- RelRefl : RelPrfTy a a ->
-- RelRefl = {a : Type} -> (x : a) -> ptyf a a (x,x)

-- public export
-- RelRefl : {a : Type} -> RelPrf a a -> Type
-- RelRefl rp = (x : a) -> rp (x,x)

-- public export
-- RelRefl : ((a : Type) -> RelPrf a a) -> Type
-- RelRefl rp = {a : Type} -> (x : a) -> rp a (x,x)


-- public export
-- RelTrans : ((a : Type) -> (b : Type) -> RelPrf a b) -> Type
-- RelTrans lprf rprf mprf = (x : a) -> (y : b) -> (z : c) -> lprf (x,y) ->
--                           rprf (y,z) -> mprf (x,z)
