---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Empty

-------------------
-- Internal imports
-------------------

import public Alpha.Algebra.Set.Ops.Compl
import public Alpha.Algebra.Set.Set
import public Alpha.Algebra.Set.Univ

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
