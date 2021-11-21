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
0 UnivPrf : SetPrf a
UnivPrf = const ()

public export
univ : Set UnivPrf
univ = const (Yes ())

public export
univProvenElem : a -> ProvenElem (UnivPrf {a})
univProvenElem x = Element x ()

------------
-- Empty set
------------

public export
0 EmptyPrf : SetPrf a
EmptyPrf = ComplPrf UnivPrf

Uninhabited (EmptyPrf x) where
  uninhabited f = f ()

public export
empty : Set EmptyPrf
empty = compl univ

public export
emptyDisprovenElem : a -> DisprovenElem (EmptyPrf {a})
emptyDisprovenElem x = Element x absurd
