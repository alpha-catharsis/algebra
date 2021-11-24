---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Singleton

-------------------
-- External imports
-------------------

import Data.DPair
import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Ops
import Alpha.Algebra.Set.Pointed
import Alpha.Algebra.Set.Set

----------------
-- Singleton set
----------------

public export
0 SinglPty : (y : a) -> SetPty a
SinglPty y x = y = x

public export
singl : DecEq a => (y : a) -> Set (SinglPty y)
singl y x = decEq y x

public export
singlProvenElem : (x : a) -> ProvenElem (SinglPty x)
singlProvenElem x = Element x Refl

------------
-- Holed set
------------

public export
0 HoledPty : (x : a) -> SetPty a
HoledPty x = ComplPty (SinglPty x)

public export
Uninhabited (HoledPty x x) where
  uninhabited f = f Refl

public export
holed : DecEq a => (x : a) -> Set (HoledPty x)
holed x = compl (singl x)

public export
holedDisprovenElem : (x : a) -> DisprovenElem (HoledPty x)
holedDisprovenElem x = Element x absurd

--------------------
-- Pointed singleton
--------------------

public export
pointedSingl : DecEq a => (x : a) -> Pointed (SinglPty x)
pointedSingl x = makePointed (singl x) (singlProvenElem x)
