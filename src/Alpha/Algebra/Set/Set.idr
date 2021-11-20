---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Set

-------------------
-- External imports
-------------------

import Data.DPair
import Decidable.Decidable

-----------------
-- Set definition
-----------------

public export
record Set (0 a : Type) where
  constructor MkSet
  0 SetPrf : (a -> Type)
  setDec : (x : a) -> Dec (SetPrf x)

public export
0 SetContra : Set a -> (x : a) -> Type
SetContra s x = Not (SetPrf s x)

public export
isElem : (x : a) -> (s : Set a) -> Dec (SetPrf s x)
isElem x s = setDec s x

public export
elem : (x : a) -> (s : Set a) -> Bool
elem x s = isYes (isElem x s)

-----------------
-- Proven element
-----------------

public export
record ProvenElem {0 a : Type} (0 s : Set a) where
  constructor MkProvenElem
  provenElem : a
  0 provenElemPrf : SetPrf s provenElem

--------------------
-- Disproven element
--------------------

public export
record DisprovenElem {0 a : Type} (0 s : Set a) where
  constructor MkDisprovenElem
  provenElem : a
  0 provenElemPrf : SetContra s provenElem

-------------------
-- Element checking
-------------------

public export
eitherProvenElem : (x : a) -> (s : Set a) ->
                   Either (DisprovenElem s) (ProvenElem s)
eitherProvenElem x s = case isElem x s of
  No contra => Left (MkDisprovenElem x contra)
  Yes prf => Right (MkProvenElem x prf)
