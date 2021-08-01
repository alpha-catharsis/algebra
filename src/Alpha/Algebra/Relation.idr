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

---------------------
-- Relation interface
---------------------

public export
interface Relation q a b | q where
    RelationPrf : (r : q) -> (x : a) -> (y : b) -> Type
    areRelated : (r : q) -> (x : a) -> (y : b) -> Dec (RelationPrf r x y)

export
related : Relation q a b => (r : q) -> (x : a) -> (y : b) -> Bool
related r x y = isYes (areRelated r x y)

----------------------
-- Relation properties
----------------------

public export
interface Relation q a a => RelationRefl q a where
  reflRelation : (r : q) -> (x : a) -> RelationPrf r x x
