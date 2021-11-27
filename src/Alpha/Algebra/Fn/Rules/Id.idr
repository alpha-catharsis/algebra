---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Fn.Rules.Id

-------------------
-- External imports
-------------------

import Data.DPair

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Fn.Basic
import Alpha.Algebra.Fn.Fn
import Alpha.Algebra.Fn.Rules.Prop
import Alpha.Algebra.Set.Set

------------------------
-- Identity is injective
------------------------

0 FnIdInjective : FnInjective Basic.fnId
FnIdInjective Refl = Refl

-------------------------
-- Identity is surjective
-------------------------

0 FnIdSurjective : FnSurjective Basic.fnId
FnIdSurjective = (y ** Refl)

------------------------
-- Identity is bijective
------------------------

0 FnIdBijective : FnBijective Basic.fnId
FnIdBijective = (FnIdInjective, FnIdSurjective)
