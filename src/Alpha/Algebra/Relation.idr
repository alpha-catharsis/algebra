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
interface Relation a b (r : (x : a) -> (y : b) -> Type) | r where
  areRelated : (x : a) -> (y : b) -> Dec (r x y)

export
related : (r : (_ : a) -> (_ : b) -> Type) -> Relation a b r => a -> b -> Bool
related r x y = isYes (areRelated {r} x y)

----------------------
-- Relation properties
----------------------

public export
interface Relation a a r => RelationRefl a r where
  reflRelation : {x : a} -> r x x

public export
interface (Relation a a r) => RelationTrans a r where
  transRelation : {x : a} -> {y : a} -> {z : a} -> r x y -> r y z -> r x z
