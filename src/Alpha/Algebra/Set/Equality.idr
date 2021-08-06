---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Relation
import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.Subset

---------------------
-- EqualSet data type
---------------------

public export
EqualSet : {a : Type} -> Rel (Set a, Set a)
EqualSet (ls,rs) = (Related (ls,rs) Subset, Related (rs,ls) Subset)

notEqualSetLeft : {ls : Set a} -> {rs : Set a} -> (Subset (ls,rs) -> Void) ->
                  EqualSet (ls,rs) -> Void
notEqualSetLeft lcontra prf = lcontra (fst prf)

notEqualSetRight : {ls : Set a} -> {rs : Set a} -> (Subset (rs,ls) -> Void) ->
                   EqualSet (ls,rs) -> Void
notEqualSetRight rcontra prf = rcontra (snd prf)

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

equivEqualSet : EquivRel EqualSet
equivEqualSet = (reflEqualSet, symEqualSet, transEqualSet)

export
antiSymSubset : AntiSymRel Subset EqualSet
antiSymSubset f g = (f,g)
