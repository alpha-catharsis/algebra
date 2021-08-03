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

import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.ProductOps
import Alpha.Decidable

---------------------
-- Relation data type
---------------------

public export
RelFpt : Type -> Type -> Type
RelFpt a b = (a,b) -> Type

public export
Rel : (fpt : RelFpt a b) -> (p : (a,b)) -> Type
Rel fpt p = fpt p

-- public export
-- data Rel : ((a,b) -> Type) -> (a,b) -> Type where
--   MkRel : {0 fpt : (a,b) -> Type} -> {p : (a,b)} -> fpt p -> Rel fpt p

----------------------
-- Relation properties
----------------------

public export
ReflRel : {a : Type} -> RelFpt a a -> Type
ReflRel fpt = (x : a) -> Rel fpt (x,x)

public export
SymmRel : {a : Type} -> RelFpt a a -> Type
SymmRel fpt = {x : a} -> {y : a} -> Rel fpt (x,y) -> Rel fpt (y,x)

public export
TransRel : {a : Type} -> RelFpt a a -> Type
TransRel fpt = {x : a} -> {y : a} -> {z : a} -> Rel fpt (x,y) ->
               Rel fpt (y,z) -> Rel fpt (x,z)

public export
AntiSymmRel : {a : Type} -> RelFpt a a -> RelFpt a a -> Type
AntiSymmRel fpt efpt = {x : a} -> {y : a} -> Rel fpt (x,y) ->
                       Rel fpt (y,x) -> Rel efpt (x,y)

-- public export
-- data ReflRel : (0 fpt : (a,a) -> Type) -> Type where
--   MkReflRel : ((x : a) -> Rel fpt (x,x)) -> ReflRel fpt

-- public export
-- data TransRel : (0 fpt : (a,a) -> Type) -> Type where
--   MkTransRel : ({x : a} -> {y : a} -> {z : a} ->
--                 Rel fpt (x,y) -> Rel fpt (y,z) -> Rel fpt (x,z)) ->
--                TransRel fpt




---------------------
-- Relation data type
---------------------

-- public export
-- data Rel : Type -> Type -> Type where
--   MkRel : (0 fpt : (a,b) -> Type) -> ((p : (a,b)) -> Dec (fpt p)) -> Rel a b

-- public export
-- 0 relFpt : Rel a b -> ((a,b) -> Type)
-- relFpt (MkRel fpt _) = fpt

-- public export
-- relDec : (r : Rel a b) -> ((p : (a,b)) -> Dec (relFpt r p))
-- relDec (MkRel _ f) = f

--------------------
-- Related data type
--------------------

-- public export
-- data Related : (a,b) -> Rel a b -> Type where
--   MkRelated : (p : (a,b)) -> (r : Rel a b) -> (prf : relFpt r p) ->
--               Related p r

-- public export
-- relatedVals : {0 p : (a,b)} -> {0 r : Rel a b} -> Related p r -> (a,b)
-- relatedVals (MkRelated p _ _) = p

-- public export
-- relatedRel : {0 p : (a,b)} -> {0 r : Rel a b} -> Related p r -> Rel a b
-- relatedRel (MkRelated _ r _) = r

-- public export
-- relatedPrf : {0 p : (a,b)} -> {0 r : Rel a b} -> Related p r -> relFpt r p
-- relatedPrf (MkRelated _ _ prf) = prf

-- export
-- notRelated : (p : (a,b)) -> (r : Rel a b) -> (relFpt r p -> Void) ->
--              Related p r -> Void
-- notRelated p r contra (MkRelated _ _ prf) = contra prf

-- export
-- areRelated : (x : a) -> (y : b) -> (r : Rel a b) -> Dec (Related (x,y) r)
-- areRelated x y r = case relDec r (x,y) of
--   Yes prf => Yes (MkRelated (x,y) r prf)
--   No contra => No (notRelated (x,y) r contra)

-- export
-- related : (x : a) -> (y : b) -> (r : Rel a b) -> Bool
-- related x y r = isYes (areRelated x y r)

-----------------------
-- Homogeneous relation
-----------------------

-- HomoRel : Type -> Type
-- HomoRel a = Rel a a

----------------------
-- Relation properties
----------------------

-- data RelRefl : HomoRel a -> Type where
--   MkRelRefl : (r : HomoRel a) -> ({0 x : a} -> Related (x, x) r) -> RelRefl r
