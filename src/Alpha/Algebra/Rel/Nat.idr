---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Nat

-------------------
-- External imports
-------------------

import Data.Nat

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Equal
import Alpha.Algebra.Rel.Prop
import Alpha.Algebra.Rel.Rel

---------------
-- LTE relation
---------------

public export
0 LTERel : Rel Nat Nat
LTERel (x,y) = LTE x y

public export
lte : DecRel LTERel
lte (x,y) = isLTE x y

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
