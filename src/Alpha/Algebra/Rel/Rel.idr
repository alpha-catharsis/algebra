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
-- RelPrf : (a : Type) -> (b : Type) -> Type
-- RelPrf a b = SetPrf (a,b)

-- public export
-- RelDec : {a : Type} -> {b : Type} -> (prf : RelPrf a b) -> Type
-- RelDec prf = (p : (a,b)) -> Dec (prf p)

-- public export
-- Rel : Type -> Type -> Type
-- Rel a b = Set (a,b)

-- public export
-- relPrf : Rel a b -> RelPrf a b
-- relPrf = setPrf

-- public export
-- relDec : (r : Rel a b) -> RelDec (relPrf r)
-- relDec = setDec

-- public export
-- areRelated : (x : a) -> (y : b) -> (r : Rel a b) -> Dec (relPrf r (x,y))
-- areRelated x y r = relDec r (x,y)

-- public export
-- related : (x : a) -> (y : b) -> (r : Rel a b) -> Bool
-- related x y r = isYes (areRelated x y r)

----------------------
-- Relation properties
----------------------

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
