---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.SingletonSet

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Relation.Relation
import Alpha.Algebra.Relation.Set
-- import Alpha.Algebra.Set.PointedSet
import Alpha.Algebra.Set.Set

----------------
-- Singleton set
----------------

public export
SingletonSet : (v : a) -> Set a
SingletonSet v x = (x = v)

public export
singletonSet : DecEq a => (v : a) -> SetDec (SingletonSet v)
singletonSet v x = decEq x v

export
disjointSingletonSets : {v : a} -> {v' : a} -> (v = v' -> Void) ->
                        Related (SingletonSet v, SingletonSet v') DisjointSets
disjointSingletonSets contra = (\veq => rewrite veq in contra,
                                \veq' => rewrite veq' in negEqSym contra)
