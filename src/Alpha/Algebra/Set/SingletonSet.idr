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

import Alpha.Algebra.Function.NullryFn
import Alpha.Algebra.Relation.Relation
import Alpha.Algebra.Relation.Set
import Alpha.Algebra.Set.PointedSet
import Alpha.Algebra.Set.Set

----------------
-- Singleton set
----------------

public export
SingletonSet : a -> Set a
SingletonSet v x = (x = v)

public export
singletonSet : DecEq a => (v : a) -> SetDec (SingletonSet v)
singletonSet v x = decEq x v

export
disjointSingletonSets : {v : a} -> {v' : a} -> (v = v' -> Void) ->
                        Related (SingletonSet v, SingletonSet v') DisjointSets
disjointSingletonSets contra = (\veq => rewrite veq in contra,
                                \veq' => rewrite veq' in negEqSym contra)


export
singletonPointedSet : {a : Type} -> DecEq a => {v : a} ->
                      SetDec (SingletonSet v) -> PointedSet (SingletonSet v)
singletonPointedSet sd = pointedSet sd (nullryFn (SingletonSet v) v)
