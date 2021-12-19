---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Prop.SetEq

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.SetEq
import Alpha.Algebra.Rel.Prop.Incl
import Alpha.Algebra.Rel.Prop.Prop
import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Set.Set

--------------------------
-- Set equality properties
--------------------------

public export
0 setEqRefl : relRefl (SetEqRel a)
setEqRefl = (inclRefl {x}, inclRefl {x})

public export
0 setEqSymm : relSymm (SetEqRel a)
setEqSymm (lprf,rprf) = (rprf,lprf)

public export
0 setEqTrans : relTrans (SetEqRel a)
setEqTrans (llprf, lrprf) (rlprf, rrprf) = (inclTrans {x} {y} {z} llprf rlprf, inclTrans {x=z} {y} {z=x} rrprf lrprf)

