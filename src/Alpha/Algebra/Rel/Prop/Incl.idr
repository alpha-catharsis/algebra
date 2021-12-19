---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Prop.Incl

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Incl
import Alpha.Algebra.Rel.Prop.Prop
import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Rel.SetEq
import Alpha.Algebra.Set.Set

---------------------------
-- Set inclusion properties
---------------------------

public export
0 inclRefl : relRefl (InclRel a)
inclRefl = id

public export
0 inclAntiSymm : relAntiSymm (InclRel a) (SetEqRel a)
inclAntiSymm lprf rprf = (lprf,rprf)

public export
0 inclTrans : relTrans (InclRel a)
inclTrans f g = g . f
