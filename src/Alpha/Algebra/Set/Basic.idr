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
0 UnivPty : SetPty a
UnivPty = const ()

public export
univ : Set UnivPty
univ = const (Yes ())

public export
univProvenElem : a -> ProvenElem (UnivPty {a})
univProvenElem x = Element x ()

------------
-- Empty set
------------

public export
0 EmptyPty : SetPty a
EmptyPty = ComplPty UnivPty

Uninhabited (EmptyPty x) where
  uninhabited f = f ()

public export
empty : Set EmptyPty
empty = compl univ

public export
emptyDisprovenElem : a -> DisprovenElem (EmptyPty {a})
emptyDisprovenElem x = Element x absurd
