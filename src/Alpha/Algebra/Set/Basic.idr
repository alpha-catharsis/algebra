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
data Univ : Type where
  MkUniv : Univ

public export
univ : Univ
univ = MkUniv

public export
0 UnivPrf : SetPrfTy a
UnivPrf _ = ()

public export
Set Univ a where
  SetPrf _ = UnivPrf

public export
DecSet Univ a where
  isElem _ _ = Yes ()

public export
univProvenElem : (x : a) -> ProvenElem {a} UnivPrf
univProvenElem x = MkProvenElem x ()

------------
-- Empty set
------------

public export
data Empty : Type where
  MkEmpty : Empty

public export
empty : Empty
empty = MkEmpty

public export
0 EmptyPrf : SetPrfTy a
EmptyPrf _ = Void

public export
Set Empty a where
  SetPrf _ = EmptyPrf

public export
DecSet Empty a where
  isElem _ _ = No absurd

public export
emptyDisprovenElem : (x : a) -> DisprovenElem {a} EmptyPrf
emptyDisprovenElem x = MkProvenElem x absurd
