---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Prop.Nat

-------------------
-- External imports
-------------------

import Data.Nat

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Equal
import Alpha.Algebra.Rel.Nat
import Alpha.Algebra.Rel.Prop.Prop
import Alpha.Algebra.Rel.Rel

-----------------
-- LTE properties
-----------------

public export
0 LTERefl : relRefl LTERel
LTERefl = reflexive {ty=Nat} {rel=LTE}

public export
0 LTEAntiSymm : relAntiSymm LTERel (EqualRel Nat Nat)
LTEAntiSymm = antisymmetric {rel=LTE} {x} {y}

public export
0 LTETrans : relTrans LTERel
LTETrans = transitive {rel=LTE} {x} {y} {z}
