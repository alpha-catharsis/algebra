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

