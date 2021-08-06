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

---------------------
-- EqualSets relation
---------------------

public export
EqualSets : {a : Type} -> Rel (Set a, Set a)
EqualSets (ls,rs) = (Related (ls,rs) Subset, Related (rs,ls) Subset)

export
notEqualSetsLeft : {ls : Set a} -> {rs : Set a} -> (Subset (ls,rs) -> Void) ->
                   EqualSets (ls,rs) -> Void
notEqualSetsLeft lcontra prf = lcontra (fst prf)

export
notEqualSetsRight : {ls : Set a} -> {rs : Set a} -> (Subset (rs,ls) -> Void) ->
                    EqualSets (ls,rs) -> Void
notEqualSetsRight rcontra prf = rcontra (snd prf)

------------------------
-- DisjointSets relation
------------------------

public export
DisjointSets : {a : Type} -> Rel (Set a, Set a)
DisjointSets (ls, rs) = ({ax : a} -> Elem ax ls -> NotElem ax rs,
                         {ax : a} -> Elem ax rs -> NotElem ax ls)

export
notDisjointSets : {x : a} -> Elem x ls -> Elem x rs ->
                  NotRelated (ls,rs) DisjointSets
notDisjointSets lprf rprf (lcontra, _) = lcontra lprf rprf

---------------------------
-- OverlappingSets relation
---------------------------

public export
OverlappingSets : {a : Type} -> Rel (Set a, Set a)
OverlappingSets (ls,rs) = (ax ** (Elem ax ls, Elem ax rs))

export
notOverlappingSets : ({ax : a} -> Elem ax ls -> NotElem ax rs) ->
                     NotRelated (ls,rs) OverlappingSets
notOverlappingSets f (ax ** (lprf, rprf)) = f lprf rprf

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
-- EqualSets projections
-----------------------

export
elemEqualSets : {x : a} -> Elem x ls -> Related (ls,rs) EqualSets -> Elem x rs
elemEqualSets prf (f,_) = f prf

export
notElemEqualSets : {x : a} -> NotElem x ls -> Related (ls,rs) EqualSets ->
                  NotElem x rs
notElemEqualSets lcontra (_,g) rprf = lcontra (g rprf)

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
-- EqualSets properties
----------------------

export
reflEqualSets : ReflRel EqualSets
reflEqualSets = (id,id)

export
symEqualSets : SymRel EqualSets
symEqualSets (f,g) = (g,f)

export
transEqualSets : TransRel EqualSets
transEqualSets (f,g) (h,i) = (h . f, g . i)

-- export
-- transEqualSets2 : TransRel2 EqualSets

export
equivEqualSets : EquivRel EqualSets
equivEqualSets = (reflEqualSets, symEqualSets, transEqualSets)

export
antiSymSubset : AntiSymRel Subset EqualSets
antiSymSubset f g = (f,g)
