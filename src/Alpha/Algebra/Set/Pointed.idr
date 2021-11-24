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
0 Pointed : SetPty a -> Type
Pointed pty = (Set pty, ProvenElem pty)

public export
makePointed : Set pty -> ProvenElem pty -> Pointed pty
makePointed s pe = (s, pe)

public export
pointedSet : Pointed pty -> Set pty
pointedSet = fst

public export
pointedProvenElem : Pointed pty -> ProvenElem pty
pointedProvenElem = snd

public export
basepoint : {0 pty : a -> Type} -> Pointed pty -> a
basepoint = provenElem . pointedProvenElem

public export
0 basepointPrf : (p : Pointed pty) -> pty (basepoint p)
basepointPrf p = provenElemPrf (pointedProvenElem p)

