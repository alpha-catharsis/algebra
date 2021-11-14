---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Complement

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Ops
import Alpha.Algebra.Set.Set

-------------------
-- Complement rules
-------------------

public export
complRule : {pty : SetPrfTy a} -> (pty x -> Void) -> ComplPrfTy pty x
complRule = id

public export
complNotRule : {pty : SetPrfTy a} -> pty x -> ComplPrfTy pty x -> Void
complNotRule pf = \f => f pf

public export
invComplRule : (ComplPrfTy pty x -> Void) -> pty x
invComplRule pf = void (pf f)
  where f : pty x -> Void
        f pf' = f pf'

public export
invComplNotRule : ComplPrfTy pty x -> pty x -> Void
invComplNotRule = id

--------------------------
-- Double complement rules
--------------------------

public export
dblComplRule : {pty : SetPrfTy a} -> pty x -> ComplPrfTy (ComplPrfTy pty) x
dblComplRule prf = \f => f prf

public export
dblComplNotRule : {pty : SetPrfTy a} -> (pty x -> Void) ->
                  ComplPrfTy (ComplPrfTy pty) x -> Void
dblComplNotRule contra = \f => f contra

public export
invDblComplRule : ComplPrfTy (ComplPrfTy pty) x -> pty x
invDblComplRule prf = void (prf f)
  where f : pty x -> Void
        f prf' = f prf'

public export
invDblComplNotRule : (ComplPrfTy (ComplPrfTy pty) x -> Void) -> pty x -> Void
invDblComplNotRule contra = \y => contra (\f => contra
                               (\g => contra (\f1 => contra (\g1 => f y))))
