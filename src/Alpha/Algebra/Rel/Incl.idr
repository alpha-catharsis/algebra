---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Incl

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Set.Set

-------------------------
-- Set inclusion relation
-------------------------

public export
0 InclPty : RelPty (SetPty a, SetPty a)
InclPty (lspty,rspty) = {e : a} -> lspty e -> rspty e

---------------------------
-- Set inclusion projection
---------------------------

public export
0 projectIncl : InclPty (lspty,rspty) -> lspty x -> rspty x
projectIncl f lprf = f lprf

public export
projectInclElem : InclPty (lspty, rspty) -> ProvenElem lspty -> ProvenElem rspty
projectInclElem f lpe = projectElem f lpe
