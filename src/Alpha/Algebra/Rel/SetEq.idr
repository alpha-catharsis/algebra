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

public export
0 setEqLeftIncl : SetEqPty (lspty,rspty) -> InclPty (lspty,rspty)
setEqLeftIncl = fst

public export
0 setEqRightIncl : SetEqPty (lspty,rspty) -> InclPty (rspty,lspty)
setEqRightIncl = snd

--------------------------
-- Set equality projection
--------------------------

public export
0 projectSetEq : SetEqPty (lspty,rspty) -> lspty x -> rspty x
projectSetEq (f,_) prf = f prf

public export
projectSetEqElem : SetEqPty (lspty, rspty) -> ProvenElem lspty ->
                   ProvenElem rspty
projectSetEqElem (f,_) lpe = projectElem f lpe
