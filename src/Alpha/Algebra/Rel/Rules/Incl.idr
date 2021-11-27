---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Rules.Incl

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Incl
import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Rel.Rules.Prop
import Alpha.Algebra.Rel.SetEq
import Alpha.Algebra.Set.Basic
import Alpha.Algebra.Set.Set

------------------------
-- Inclusion is relexive
------------------------

public export
0 inclRefl : RelRefl InclPty
inclRefl lpty = lpty

--------------------------
-- Inclusion is transitive
--------------------------

public export
0 inclTrans : RelTrans InclPty
inclTrans f g lprf = g (f lprf)

------------------------------
-- Inclusion is anti-symmetric
------------------------------

public export
0 inclAntiSymm : RelAntiSymm InclPty SetEqPty
inclAntiSymm f f' = (f,f')

-------------------------
-- Universe set inclusion
-------------------------

public export
0 inclUniv : InclPty (lspty,UnivPty)
inclUniv _ = ()

----------------------
-- Empty set inclusion
----------------------

public export
0 inclEmpty : InclPty (EmptyPty,rspty)
inclEmpty prf = void (prf ())

