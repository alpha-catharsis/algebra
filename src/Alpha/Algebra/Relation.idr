---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Relation

-------------------
-- External imports
-------------------

import Data.Bool
import Decidable.Decidable

---------------------
-- Relation data type
---------------------

public export
RelFpt : (Type,Type) -> Type
RelFpt (a,b) = (a,b) -> Type

public export
RelPrf : RelFpt (a,b) -> (a,b) -> Type
RelPrf fpt p = fpt p

public export
RelContra : RelFpt (a,b) -> (a,b) -> Type
RelContra fpt p = RelPrf fpt p -> Void

public export
RelFn : {a : Type} -> {b : Type} -> RelFpt (a,b) -> Type
RelFn fpt = (p : (a,b)) -> Dec (fpt p)

public export
areRelated : {fpt : RelFpt (a,b)} -> (p : (a,b)) -> RelFn fpt -> Dec (fpt p)
areRelated p fn = fn p

public export
related : {fpt : RelFpt (a,b)} -> (p : (a,b)) -> RelFn fpt -> Bool
related p fn = isYes (areRelated p fn)

----------------------
-- Relation properties
----------------------

public export
ReflRel : {a : Type} -> RelFpt (a,a) -> Type
ReflRel fpt = {p : (a,a)} -> RelPrf fpt p

public export
SymRel : {a : Type} -> RelFpt (a,a) -> Type
SymRel fpt = {p : (a,a)} -> RelPrf fpt p -> RelPrf fpt (snd p, fst p)

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
