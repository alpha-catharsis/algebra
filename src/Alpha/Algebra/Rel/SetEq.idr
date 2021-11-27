---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.SetEq

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Rel.Incl
import Alpha.Algebra.Set.Set

------------------------
-- Set equality relation
------------------------

public export
0 SetEqPty : RelPty (SetPty a, SetPty a)
SetEqPty (lspty,rspty) = (InclPty (lspty,rspty), InclPty (rspty,lspty))

--------------------------
-- Set equality projection
--------------------------

public export
0 projectSetEq : SetEqPty (lpty,rpty) -> lpty x -> rpty x
projectSetEq (f,_) prf = f prf

public export
projectSetEqElem : SetEqPty (lpty, rpty) -> ProvenElem lpty -> ProvenElem rpty
projectSetEqElem (f,_) lpe = projectElem f lpe
