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
0 SinglPrf : (y : a) -> SetPrf a
SinglPrf y x = y = x

public export
singl : DecEq a => (y : a) -> Set (SinglPrf y)
singl y x = decEq y x

public export
singlProvenElem : (x : a) -> ProvenElem (SinglPrf x)
singlProvenElem x = Element x Refl

------------
-- Holed set
------------

public export
0 HoledPrf : (x : a) -> SetPrf a
HoledPrf x = ComplPrf (SinglPrf x)

public export
Uninhabited (HoledPrf x x) where
  uninhabited f = f Refl

public export
holed : DecEq a => (x : a) -> Set (HoledPrf x)
holed x = compl (singl x)

public export
holedDisprovenElem : (x : a) -> DisprovenElem (HoledPrf x)
holedDisprovenElem x = Element x absurd

--------------------
-- Pointed singleton
--------------------

public export
pointedSingl : DecEq a => (x : a) -> Pointed (SinglPrf x)
pointedSingl x = makePointed (singl x) (singlProvenElem x)
