---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Fn.Prop

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Fn.Fn
import Alpha.Algebra.Set.Set

----------------------
-- Function properties
----------------------

public export
0 FnInjective : Fn d c -> Type
FnInjective f = (x : ProvenElem d) -> (x' : ProvenElem d) -> f x = f x' -> x = x'

public export
0 FnSurjective : Fn d c -> Type
FnSurjective f = (y : ProvenElem c) -> (x : ProvenElem d ** f x = y)

public export
0 FnBijective : Fn d c -> Type
FnBijective f = (FnInjective f, FnSurjective f)
