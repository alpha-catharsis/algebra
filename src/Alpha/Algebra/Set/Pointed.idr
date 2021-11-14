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
data Pointed : SetPrfTy a -> Type where
  MkPointed : {0 pty : SetPrfTy a} -> (0 s : Set pty) -> ProvenElem pty ->
              Pointed pty


public export
0 pointedSet : Pointed pty -> Set pty
pointedSet (MkPointed s _) = s

public export
pointedProven : Pointed pty -> ProvenElem pty
pointedProven (MkPointed _ pe) = pe

public export
basepoint : {0 a : Type} -> {0 pty : SetPrfTy a} -> Pointed pty -> a
basepoint = provenElem . pointedProven

public export
0 pointedPrf : (p : Pointed pty) -> pty (basepoint p)
pointedPrf p = provenElemPrf (pointedProven p)
