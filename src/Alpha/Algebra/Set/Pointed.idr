---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Pointed

-------------------
-- External imports
-------------------

import Data.DPair

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

--------------
-- Pointed set
--------------

public export
record Pointed (0 a : Type) where
  constructor MkPointed
  pointedSet : Set a
  pointedProven : ProvenElem pointedSet

public export
basepoint : Pointed a -> a
basepoint p = provenElem (pointedProven p)

public export
0 basepointPrf : (p : Pointed a) -> SetPrf (pointedSet p) (basepoint p)
basepointPrf p = provenElemPrf (pointedProven p)
