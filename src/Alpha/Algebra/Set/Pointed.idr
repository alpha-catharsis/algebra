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
interface Set t a => Pointed t a | t where
  basepointElem : (s : t) -> SetProvenElem s

public export
basepoint : Pointed t a => t -> a
basepoint ps = provenElem (basepointElem ps)

public export
0 basepointPrf : Pointed t a => (ps : t) -> SetPrf ps (basepoint ps)
basepointPrf ps = elemPrf (basepointElem ps)
