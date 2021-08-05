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
Related : (a,b) -> RelFpt (a,b) -> Type
Related p fpt = fpt p

public export
NotRelated : (a,b) -> RelFpt (a,b) -> Type
NotRelated fpt p = Related fpt p -> Void

public export
Rel : {a : Type} -> {b : Type} -> RelFpt (a,b) -> Type
Rel fpt = (p : (a,b)) -> Dec (fpt p)

public export
areRelated : {fpt : RelFpt (a,b)} -> (p : (a,b)) -> Rel fpt -> Dec (fpt p)
areRelated p fn = fn p

public export
related : {fpt : RelFpt (a,b)} -> (p : (a,b)) -> Rel fpt -> Bool
related p fn = isYes (areRelated p fn)

----------------------
-- Relation properties
----------------------

public export
ReflRel : {a : Type} -> RelFpt (a,a) -> Type
ReflRel fpt = {p : (a,a)} -> Related p fpt

public export
SymRel : {a : Type} -> RelFpt (a,a) -> Type
SymRel fpt = {p : (a,a)} -> Related p fpt -> Related (snd p, fst p) fpt

public export
TransRel : {a : Type} -> RelFpt (a,a) -> Type
TransRel fpt = {x : a} -> {y : a} -> {z : a} -> Related (x,y) fpt ->
               Related (y,z) fpt -> Related (x,z) fpt

public export
EquivRel : {a : Type} -> RelFpt (a,a) -> Type
EquivRel fpt = (ReflRel fpt, SymRel fpt, TransRel fpt)

public export
AntiSymRel : {a : Type} -> RelFpt (a,a) -> RelFpt (a,a) -> Type
AntiSymRel fpt efpt = {x : a} -> {y : a} -> Related (x,y) fpt ->
                       Related (y,x) fpt -> Related (x,y) efpt
