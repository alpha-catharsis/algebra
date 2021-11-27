---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Rules.SetEq

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Incl
import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Rel.Rules.Incl
import Alpha.Algebra.Rel.Rules.Prop
import Alpha.Algebra.Rel.SetEq
import Alpha.Algebra.Set.Set

---------------------------
-- Set equality is relexive
---------------------------

public export
0 setEqualRefl : RelRefl SetEqPty
setEqualRefl = (inclRefl {x},inclRefl {x})

----------------------------
-- Set equality is symmetric
----------------------------

public export
0 setEqualSymm : RelSymm SetEqPty
setEqualSymm (f,f') = (f',f)

-----------------------------
-- Set equality is transitive
-----------------------------

public export
0 setEqualTrans : RelTrans SetEqPty
setEqualTrans (f,f') (g,g') = (g . f, f' . g')

