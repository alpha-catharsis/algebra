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

---------------------
-- Relation data type
---------------------

public export
data Rel : (a -> b -> Type) -> Type -> Type -> Type where
  MkRel : {0 fpt : a -> b -> Type} -> ((x : a) -> (y : b) -> Dec (fpt x y)) ->
          Rel fpt a b

export
relDec : Rel fpt a b -> ((x : a) -> (y : b) -> Dec (fpt x y))
relDec (MkRel f) = f

--------------------
-- Related data type
--------------------

public export
data Related : a -> b -> Rel fpt a b -> Type where
  MkRelated : (x : a) -> (y : b) -> (r : Rel fpt a b) -> (prf : fpt x y) ->
              Related x y r

export
notRelated : (x : a) -> (y : b) -> (r : Rel fpt a b) -> (fpt x y -> Void) ->
             Related x y r -> Void
notRelated x y r contra (MkRelated x y r prf) = contra prf

export
areRelated : (x : a) -> (y : b) -> (r : Rel fpt a b) -> Dec (Related x y r)
areRelated x y (MkRel f) = case f x y of
  Yes prf => Yes (MkRelated x y (MkRel f) prf)
  No contra => No (notRelated x y (MkRel f) contra)

export
related : (x : a) -> (y : b) -> (r : Rel fpt a b) -> Bool
related x y r@(MkRel _) = isYes (areRelated x y r)
