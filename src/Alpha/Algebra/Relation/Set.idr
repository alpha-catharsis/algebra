---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Relation.Set

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Relation.Relation
import Alpha.Algebra.Set.Set

------------------
-- Subset relation
------------------

public export
Subset : {a : Type} -> Rel (Set a, Set a)
Subset (ls,rs) = ({ax : a} -> Elem ax ls -> Elem ax rs)

export
notSubset : {x : a} -> Elem x ls -> (Elem x rs -> Void) ->
            NotRelated (ls,rs) Subset
notSubset lprf rcontra f = rcontra (f lprf)

--------------------
-- EqualSet relation
--------------------

public export
EqualSet : {a : Type} -> Rel (Set a, Set a)
EqualSet (ls,rs) = (Related (ls,rs) Subset, Related (rs,ls) Subset)

export
notEqualSetLeft : {ls : Set a} -> {rs : Set a} -> (Subset (ls,rs) -> Void) ->
                  EqualSet (ls,rs) -> Void
notEqualSetLeft lcontra prf = lcontra (fst prf)

export
notEqualSetRight : {ls : Set a} -> {rs : Set a} -> (Subset (rs,ls) -> Void) ->
                   EqualSet (ls,rs) -> Void
notEqualSetRight rcontra prf = rcontra (snd prf)

--------------------
-- Subset projection
--------------------

export
elemSubset : {x : a} -> Elem x ls -> Related (ls,rs) Subset -> Elem x rs
elemSubset prf f = f prf

export
notElemSubset : {x : a} -> NotElem x rs -> Related (ls, rs) Subset ->
                NotElem x ls
notElemSubset contra f prf = contra (f prf)

-----------------------
-- EqualSet projections
-----------------------

export
elemEqualSet : {x : a} -> Elem x ls -> Related (ls,rs) EqualSet -> Elem x rs
elemEqualSet prf (f,_) = f prf

export
notElemEqualSet : {x : a} -> NotElem x ls -> Related (ls,rs) EqualSet ->
                  NotElem x rs
notElemEqualSet lcontra (_,g) rprf = lcontra (g rprf)

--------------------
-- Subset properties
--------------------

export
reflSubset : ReflRel Subset
reflSubset = id

export
transSubset : TransRel Subset
transSubset f g = g . f

----------------------
-- EqualSet properties
----------------------

export
reflEqualSet : ReflRel EqualSet
reflEqualSet = (id,id)

export
symEqualSet : SymRel EqualSet
symEqualSet (f,g) = (g,f)

export
transEqualSet : TransRel EqualSet
transEqualSet (f,g) (h,i) = (h . f, g . i)

-- export
-- transEqualSet2 : TransRel2 EqualSet

export
equivEqualSet : EquivRel EqualSet
equivEqualSet = (reflEqualSet, symEqualSet, transEqualSet)

export
antiSymSubset : AntiSymRel Subset EqualSet
antiSymSubset f g = (f,g)
