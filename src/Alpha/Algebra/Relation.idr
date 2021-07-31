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
-- import Alpha.Decidable

---------------------
-- Relation interface
---------------------

public export
interface (Set t a, Set u b) => Relation q t u a b where
  RelationPrf : (r : q) -> (ls : t) -> (rs : u) ->
                (x : a) -> (y : b) -> Type
  areRelated : (r : q) -> (ls : t) -> (rs : u) ->
               (x : a) -> (y : b) ->
               SetElemPrf x ls -> SetElemPrf y rs ->
               Dec (RelationPrf r ls rs x y)

related : Relation q t u a b => (r : q) -> (ls : t) -> (rs : u) ->
          (x : a) -> (y : b) ->
          {auto lprf : SetElemPrf x ls} -> {auto rprf : SetElemPrf y rs} ->
          Bool
related r ls rs x y = isYes (areRelated r ls rs x y lprf rprf)


----------------------
-- Relation properties
----------------------

public export
interface Relation q t t a a => RelationRefl q t a where
  reflRelation : (r : q) -> (s : t) -> (x : a) -> (y : a) ->
                 RelationPrf r s s x y ->
                 RelationPrf r s s y x
