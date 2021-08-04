---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Relation

-------------------
-- External imports
-------------------

import Data.Bool
import Decidable.Decidable

-------------------
-- Internal imports
-------------------

-- import Alpha.Algebra.Set.Set
-- import Alpha.Algebra.Set.ProductOps
-- import Alpha.Decidable

---------------------
-- Relation data type
---------------------

-- public export
-- RelFpt : Type -> Type -> Type
-- RelFpt a b = (a,b) -> Type

-- public export
-- RelPrf : RelFpt a b -> (a,b) -> Type
-- RelPrf fpt p = fpt p

-- public export
-- RelDec : RelFpt a b -> (a,b) -> Type
-- RelDec fpt p = Dec (RelPrf fpt p)

-- export
-- related : RelDec fpt (x,y) -> Bool
-- related d = isYes d

----------------------
-- Relation properties
----------------------

-- public export
-- ReflRel : {a : Type} -> RelFpt a a -> Type
-- ReflRel fpt = (x : a) -> RelPrf fpt (x,x)

-- public export
-- SymmRel : {a : Type} -> RelFpt a a -> Type
-- SymmRel fpt = {x : a} -> {y : a} -> RelPrf fpt (x,y) -> RelPrf fpt (y,x)

-- public export
-- TransRel : {a : Type} -> RelFpt a a -> Type
-- TransRel fpt = {x : a} -> {y : a} -> {z : a} -> RelPrf fpt (x,y) ->
--                RelPrf fpt (y,z) -> RelPrf fpt (x,z)

-- public export
-- EquivRel : {a : Type} -> RelFpt a a -> Type
-- EquivRel fpt = (ReflRel fpt, SymmRel fpt, TransRel fpt)

-- public export
-- AntiSymmRel : {a : Type} -> RelFpt a a -> RelFpt a a -> Type
-- AntiSymmRel fpt efpt = {x : a} -> {y : a} -> RelPrf fpt (x,y) ->
--                        RelPrf fpt (y,x) -> RelPrf efpt (x,y)
