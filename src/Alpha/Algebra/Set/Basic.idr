---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Basic

-------------------
-- External imports
-------------------

import Data.DPair

-------------------
-- Internal imports
-------------------

import public Alpha.Algebra.Set.Ops
import public Alpha.Algebra.Set.Set

---------------
-- Universe set
---------------

public export
0 UnivPrfTy : SetPrfTy a
UnivPrfTy = const ()

public export
univ : Set UnivPrfTy
univ = const (Yes ())

public export
univProven : a -> ProvenElem (UnivPrfTy {a})
univProven x = Element x ()

------------
-- Empty set
------------

public export
0 EmptyPrfTy : SetPrfTy a
EmptyPrfTy = ComplPrfTy UnivPrfTy

Uninhabited (EmptyPrfTy x) where
  uninhabited f = f ()

public export
empty : Set EmptyPrfTy
empty = compl univ

public export
emptyDisproven : a -> DisprovenElem (EmptyPrfTy {a})
emptyDisproven x = Element x absurd
