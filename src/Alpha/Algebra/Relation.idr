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

import Alpha.Algebra.Set
import Alpha.Decidable

---------------------
-- Relation data type
---------------------

public export
data Rel : Set a -> Set b -> Type where
  MkRel : {0 ls : Set a} -> {0 rs : Set b} ->
          (0 fpt : (a, b) -> Type) ->
          ({0 p : (a, b)} -> (e : Elem p (product ls rs)) ->
           Dec (fpt p)) ->
          Rel ls rs

public export
0 relFpt : {0 ls : Set a} -> {0 rs : Set b} -> Rel ls rs -> ((a, b) -> Type)
relFpt (MkRel fpt _) = fpt

public export
relDec : {0 ls : Set a} -> {0 rs : Set b} -> (r : Rel ls rs) ->
         ({0 p : (a, b)} -> (e : Elem p (product ls rs)) ->
          Dec (relFpt r p))
relDec (MkRel _ f) = f

--------------------
-- Related data type
--------------------

public export
data Related : {0 ls : Set a} -> {0 rs : Set b} -> Rel ls rs -> (a, b) ->
               Type where
  MkRelated : {0 ls : Set a} -> {0 rs : Set b} -> (r : Rel ls rs) ->
              {p : (a, b)} -> Elem p (product ls rs) ->
              relFpt r p -> Related r p

export
notRelated : {0 ls : Set a} -> {0 rs : Set b} -> (r : Rel ls rs) ->
             {p : (a, b)} -> Elem p (product ls rs) ->
             (relFpt r p -> Void) -> Related r p -> Void
notRelated r e contra (MkRelated _ _ prf) = contra prf

export
areRelated : {ls : Set a} -> {rs : Set b} -> (r : Rel ls rs) ->
               (x : a) -> (y : b) ->
               {auto leprf : Elem x ls} -> {auto reprf : Elem y rs} ->
               Dec (Related r (x, y))
areRelated r x y = let ep = elemProduct leprf reprf in case relDec r ep of
  Yes prf => Yes (MkRelated r ep prf)
  No contra => No (notRelated r ep contra)

export
related : {ls : Set a} -> {rs : Set b} -> (r : Rel ls rs) ->
          (x : a) -> (y : b) ->
          {auto leprf : Elem x ls} -> {auto reprf : Elem y rs} ->
          Bool
related r x y = isYes (areRelated r x y {leprf} {reprf})



