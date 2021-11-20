---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.SetEqual

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Rel.Inclusion
import Alpha.Algebra.Set.Set

----------------------
-- SetEqual definition
----------------------

public export
0 SetEqualPrfTy : RelPrfTy (SetPrfTy a) (SetPrfTy a)
SetEqualPrfTy (lpty,rpty) = (InclPrfTy (lpty,rpty), InclPrfTy (rpty,lpty))

public export
0 SetEqualRefl : RelRefl SetEqualPrfTy
SetEqualRefl = (\lprf, rprf => rprf, \rpf, lprf => lprf)

public export
0 InclAsymm : RelAsymm InclPrfTy SetEqualPrfTy
InclAsymm lprf rprf = (lprf, rprf)

public export
0 setEqual : {pty : SetPrfTy a} -> SetEqualPrfTy (pty,pty)
setEqual = (inclRefl, inclRefl)

public export
0 setEqualElem : {x : a} -> {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} ->
             SetEqualPrfTy (lpty,rpty) -> lpty x -> rpty x
setEqualElem f lprf = fst f x lprf
