---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Relation.Relation

-------------------
-- External imports
-------------------

import Data.Bool
import Decidable.Decidable

---------------------
-- Relation data type
---------------------

public export
Rel : (Type,Type) -> Type
Rel (a,b) = (a,b) -> Type

public export
Related : (a,b) -> Rel (a,b) -> Type
Related p r = r p

public export
NotRelated : (a,b) -> Rel (a,b) -> Type
NotRelated r p = Related r p -> Void

public export
RelDec : {a : Type} -> {b : Type} -> Rel (a,b) -> Type
RelDec r = (p : (a,b)) -> Dec (r p)

public export
areRelated : {r : Rel (a,b)} -> (p : (a,b)) -> RelDec r -> Dec (r p)
areRelated p fn = fn p

public export
related : {r : Rel (a,b)} -> (p : (a,b)) -> RelDec r -> Bool
related p fn = isYes (areRelated p fn)

----------------------
-- Relation properties
----------------------

public export
ReflRel : {a : Type} -> Rel (a,a) -> Type
ReflRel r = {x : a} -> Related (x,x) r

public export
SymRel : {a : Type} -> Rel (a,a) -> Type
SymRel r = {x : a} -> {y : a} -> Related (x,y) r -> Related (y,x) r

public export
TransRel : {a : Type} -> Rel (a,a) -> Type
TransRel r = {x : a} -> {y : a} -> {z : a} -> Related (x,y) r ->
             Related (y,z) r -> Related (x,z) r

-- public export
-- TransRel2 : ((pt : (Type, Type)) -> Type) -> Type
-- TransRel2 fr = {d : Type} -> {e : Type} -> {f : Type} ->
--                {x : d} -> {y : e} -> {z : f} ->
--                {lr : fr (d,e)} -> {rr : fr (e,f)} -> {r : fr (d,f)} ->
--                Related (x,y) lr {a=d} {b=e} -> Related (y,z) rr ->
--                Related (x,z) r

public export
AntiSymRel : {a : Type} -> Rel (a,a) -> Rel (a,a) -> Type
AntiSymRel r er = {x : a} -> {y : a} -> Related (x,y) r ->
                  Related (y,x) r -> Related (x,y) er
