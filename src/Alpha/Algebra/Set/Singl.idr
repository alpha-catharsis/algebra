---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Singl

-------------------
-- External imports
-------------------

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
0 SinglSet : (x : a) -> Set a
SinglSet x y = y = x

public export
singl : DecEq a => (x : a) -> DecSet (SinglSet x)
singl x y = decEq y x

public export
singlProvenElem : (x : a) -> ProvenElem (SinglSet x)
singlProvenElem x = MkProvenElem x Refl

------------
-- Holed set
------------

public export
0 HoledSet : (x : a) -> Set a
HoledSet x = Compl (SinglSet x)

public export
holed : DecEq a => (x : a) -> DecSet (HoledSet x)
holed x = compl (singl x)

public export
Uninhabited (HoledSet x x) where
  uninhabited f = f Refl

public export
holedDisprovenElem : (x : a) -> DisprovenElem (HoledSet x)
holedDisprovenElem x = MkProvenElem x absurd

--------------------
-- Pointed singleton
--------------------

public export
pointedSingl : (x : a) -> Pointed (SinglSet x)
pointedSingl x = MkPointed (SinglSet x) x Refl

public export
decPointedSingl : DecEq a => (x : a) -> DecPointed (SinglSet x)
decPointedSingl x = MkDecPointed (pointedSingl x) (singl x)
