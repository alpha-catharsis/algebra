---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Singl

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
data Singl : Type -> Type where
  MkSingl : (x : a) -> Singl a

public export
singl : (x : a) -> Singl a
singl = MkSingl

public export
0 SinglPrf : a -> SetPrfTy a
SinglPrf v x = x = v

public export
Set (Singl a) a where
  SetPrf (MkSingl v) = SinglPrf v

public export
DecEq a => DecSet (Singl a) a where
  isElem x (MkSingl v) = decEq x v

public export
singlProvenElem : (v : a) -> SetProvenElem (singl v)
singlProvenElem v = MkProvenElem v Refl

------------
-- Holed set
------------

public export
Holed : Type -> Type
Holed a = Compl (Singl a) a

public export
holed : (x : a) -> Holed a
holed x = compl (singl x)

public export
0 HoledPrf : a -> SetPrfTy a
HoledPrf v = ComplPrf (singl v)

public export
Uninhabited (HoledPrf x x) where
  uninhabited f = f Refl

public export
holedDisprovenElem : (v : a) -> DisprovenElem (HoledPrf v)
holedDisprovenElem v = MkProvenElem v absurd

--------------------
-- Pointed singleton
--------------------

public export
DecEq a => Pointed (Singl a) a where
  basepointElem (MkSingl v) = singlProvenElem v
