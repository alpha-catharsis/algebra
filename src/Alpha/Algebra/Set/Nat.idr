---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Nat

-------------------
-- Internal imports
-------------------

import public Alpha.Algebra.Set.Basic
import public Alpha.Algebra.Set.Set

----------
-- Nat set
----------

public export
0 NatPrfTy : SetPrfTy Nat
NatPrfTy = UnivPrfTy

public export
nat : Set NatPrfTy
nat = univ
