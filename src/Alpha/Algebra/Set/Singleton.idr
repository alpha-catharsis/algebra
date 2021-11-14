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
0 SinglPrfTy : (x : a) -> SetPrfTy a
SinglPrfTy y x = y = x

public export
singl : DecEq a => (x : a) -> Set (SinglPrfTy x)
singl y x = decEq y x

public export
singlProven : (x : a) -> ProvenElem (SinglPrfTy x)
singlProven x = Element x Refl

------------
-- Holed set
------------

public export
0 HoledPrfTy : (x : a) -> SetPrfTy a
HoledPrfTy x = ComplPrfTy (SinglPrfTy x)

Uninhabited (HoledPrfTy x x) where
  uninhabited f = f Refl

public export
holed : DecEq a => (x : a) -> Set (HoledPrfTy x)
holed x = compl (singl x)

public export
holedDisproven : DecEq a => (x : a) -> DisprovenElem (HoledPrfTy x)
holedDisproven x = Element x absurd

--------------------
-- Pointed singleton
--------------------

public export
pointedSingl : DecEq a => (x : a) -> Pointed (SinglPrfTy x)
pointedSingl x = MkPointed (singl x) (Element x Refl)
