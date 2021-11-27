---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Fn.Rules.Prop

-------------------
-- External imports
-------------------

import Data.DPair

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Fn.Fn
import Alpha.Algebra.Set.Set

---------------------
-- Injective function
---------------------

public export
0 FnInjective : Fn lpty rpty -> Type
FnInjective f = {x : ProvenElem lpty} -> {x' : ProvenElem lpty} ->
                f x = f x' -> x = x'

public export
0 FnSurjective : Fn lpty rpty -> Type
FnSurjective f = {y : ProvenElem rpty} -> (x : ProvenElem lpty ** f x = y)

public export
0 FnBijective : Fn lpty rpty -> Type
FnBijective f = (FnInjective f, FnSurjective f)
