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
Subset : {a : Type} -> {lfpt : SetFpt a} -> {rfpt : SetFpt a} ->
         RelFpt (Set lfpt, Set rfpt)
Subset _ = ({ax : a} -> Elem ax lfpt -> Elem ax rfpt)

export
notSubset : {a : Type} -> {lfpt : SetFpt a} -> {rfpt : SetFpt a} ->
            {ls : Set lfpt} -> {rs : Set rfpt} ->
            {x : a} -> Elem x lfpt -> (Elem x rfpt -> Void) ->
            NotRelated (ls,rs) Subset
notSubset lprf rcontra f = rcontra (f lprf)

--------------------
-- Subset properties
--------------------

export
reflSubset : ReflRel Subset
reflSubset = id

-- export
-- transSubset : TransRel Subset
-- transSubset f g = g . f
