---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Pointed

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

--------------
-- Pointed set
--------------

public export
Pointed : {a : Type} -> SetPrfTy a -> Type
Pointed pty = (Set pty, ProvenElem pty)

public export
pointedSet : Pointed pty -> Set pty
pointedSet = fst

public export
pointedProven : Pointed pty -> ProvenElem pty
pointedProven = snd

public export
basepoint : {a : Type} -> {pty : SetPrfTy a} -> Pointed pty -> a
basepoint = provenElem . pointedProven

public export
pointedPrf : (p : Pointed pty) -> pty (basepoint p)
pointedPrf p = provenElemPrf (pointedProven p)
