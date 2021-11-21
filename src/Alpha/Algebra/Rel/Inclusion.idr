---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Inclusion

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Set.Basic
import Alpha.Algebra.Set.Rules.Complement
import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.Singleton

-----------------------
-- Inclusion definition
-----------------------

-- public export
-- 0 InclPrf : Set a -> Set a -> Type
-- InclPrf ls rs = (x : a) -> SetPrf ls x -> SetPrf rs x

-- inclUniv : Rel (sets {a}) (sets {a})
-- inclUniv = MkRel (\px,py => )

-- public export
-- 0 InclPrfTy : RelPrfTy (SetPrfTy a) (SetPrfTy a)
-- InclPrfTy (lpty,rpty) = ((x : a) -> lpty x -> rpty x)

-- public export
-- 0 inclRefl : RelRefl InclPrfTy
-- inclRefl _ prf = prf

-- public export
-- 0 inclTrans : RelTrans InclPrfTy
-- inclTrans lprf mprf x lprf' = mprf x (lprf x lprf')

-- public export
-- 0 inclUniv : InclPrfTy (lpty, UnivPrfTy)
-- inclUniv _ _ = ()

-- public export
-- 0 inclEmpty : InclPrfTy (EmptyPrfTy, rpty)
-- inclEmpty _ prf = void (prf ())

-- public export
-- 0 inclElem : {x : a} -> {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} ->
--              InclPrfTy (lpty,rpty) -> lpty x -> rpty x
-- inclElem f lprf = f x lprf
