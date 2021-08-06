---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Subset

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
import Alpha.Algebra.Relation

-------------------
-- Subset data type
-------------------

public export
Subset : {a : Type} -> Rel (Set a, Set a)
Subset (ls,rs) = ({ax : a} -> Elem ax ls -> Elem ax rs)

export
notSubset : {x : a} -> Elem x ls -> (Elem x rs -> Void) ->
            NotRelated (ls,rs) Subset
notSubset lprf rcontra f = rcontra (f lprf)

--------------------
-- Subset properties
--------------------

export
reflSubset : ReflRel Subset
reflSubset = id

export
transSubset : TransRel Subset
transSubset f g = g . f

--------------------
-- Subset projection
--------------------

elemSubset : {x : a} -> Elem x ls -> Related (ls,rs) Subset -> Elem x rs
elemSubset prf f = f prf
