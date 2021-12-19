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
UnivSet : Set a
UnivSet _ = ()

public export
univ : DecSet UnivSet
univ _ = Yes ()

public export
univProvenElem : (x : a) -> ProvenElem {a} UnivSet
univProvenElem x = MkProvenElem x ()

------------
-- Empty set
------------

public export
EmptySet : Set a
EmptySet = Compl UnivSet

public export
empty : DecSet EmptySet
empty = compl univ

public export
Uninhabited (EmptySet x) where
  uninhabited () impossible

public export
emptyDisprovenElem : (x : a) -> DisprovenElem {a} EmptySet
emptyDisprovenElem x = MkProvenElem x absurd
