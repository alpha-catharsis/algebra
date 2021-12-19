---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Prop.Equal

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Equal
import Alpha.Algebra.Rel.Prop.Prop
import Alpha.Algebra.Rel.Rel

-------------------
-- Equal properties
-------------------

public export
0 equalRefl : relRefl (EqualRel a a)
equalRefl = Refl

public export
0 equalSymm : relSymm (EqualRel a a)
equalSymm Refl = Refl

public export
0 equalTrans : relTrans (EqualRel a a)
equalTrans lprf rprf = rewrite lprf in rprf
