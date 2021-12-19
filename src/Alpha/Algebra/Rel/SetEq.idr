---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.SetEq

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Incl
import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Set.Set

------------------------
-- Set equality relation
------------------------

public export
0 SetEqRel : (a : Type) -> Rel (Set a) (Set a)
SetEqRel a (ls,rs) = (InclRel a (ls,rs), InclRel a (rs,ls))

--------------------------
-- Set equality projection
--------------------------

public export
0 projectSetEq : SetEqRel a (ls,rs) -> ls x -> rs x
projectSetEq (lf,_) prf = projectIncl {ls} {rs} lf prf

public export
projectSetEqElem : (0 eprf : SetEqRel a (ls,rs)) -> ProvenElem ls -> ProvenElem rs
projectSetEqElem (lf,_) pe = projectInclElem {ls} {rs} lf pe
