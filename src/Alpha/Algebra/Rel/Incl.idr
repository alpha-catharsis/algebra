---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Incl

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Prop
import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Set.Set

-------------------------
-- Set inclusion relation
-------------------------

public export
0 InclRel : (a : Type) -> Rel (Set a) (Set a)
InclRel a (ls,rs) = {0 e : a} -> ls e -> rs e

---------------------------
-- Set inclusion properties
---------------------------

public export
0 inclRefl : relRefl (InclRel a)
inclRefl = id

public export
0 inclTrans : relTrans (InclRel a)
inclTrans f g = g . f

---------------------------
-- Set inclusion projection
---------------------------

public export
0 projectIncl : InclRel a (ls,rs) -> ls x -> rs x
projectIncl f lprf = f lprf

public export
projectInclElem : (0 iprf : InclRel a (ls,rs)) -> ProvenElem ls -> ProvenElem rs
projectInclElem f pe = projectElem f pe
