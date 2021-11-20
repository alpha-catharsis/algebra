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
singl : DecEq a => (x : a) -> Set a
singl y = MkSet (\x => y=x) (\x => decEq y x)

public export
singlProvenElem : DecEq a => (x : a) -> ProvenElem (singl x)
singlProvenElem x = MkProvenElem x Refl

------------
-- Holed set
------------

public export
holed : DecEq a => (x : a) -> Set a
holed x = compl (singl x)

{x : a} -> DecEq a => Uninhabited (SetPrf (holed x) x) where
  uninhabited f = f Refl

public export
holedDisproven : DecEq a => (x : a) -> DisprovenElem (holed x)
holedDisproven x = MkDisprovenElem x absurd

--------------------
-- Pointed singleton
--------------------

public export
pointedSingl : DecEq a => (x : a) -> Pointed a
pointedSingl x = MkPointed (singl x) (singlProvenElem x)
