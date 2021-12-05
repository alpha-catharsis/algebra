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
0 SetPrfTy : Type -> Type
SetPrfTy a = a -> Type

public export
interface Set t a | t where
  0 SetPrf : t -> SetPrfTy a

public export
interface Set t a => DecSet t a | t where
  isElem : (x : a) -> (s : t) -> Dec (SetPrf s x)

public export
elem : DecSet t a => (x : a) -> (s : t) -> Bool
elem x s = isYes (isElem x s)

--------------------------------
-- Proven and disproven elements
--------------------------------

public export
record ProvenElem {0 a : Type} (0 prfTy : SetPrfTy a) where
  constructor MkProvenElem
  provenElem : a
  0 elemPrf : prfTy provenElem

public export
0 DisprovenElem : SetPrfTy a -> Type
DisprovenElem prfTy = ProvenElem (Not . prfTy)

public export
projectElem : {0 prfTy : SetPrfTy a} -> {0 prfTy' : SetPrfTy a} ->
              (0 f : {x : a} -> prfTy x -> prfTy' x) ->
              ProvenElem prfTy -> ProvenElem prfTy'
projectElem f pe = MkProvenElem (provenElem pe) (f (elemPrf pe))


public export
0 EitherElem : SetPrfTy a -> Type
EitherElem prfTy = Either (DisprovenElem prfTy) (ProvenElem prfTy)

public export
eitherElem : DecSet t a => (x : a) -> (s : t) -> EitherElem (SetPrf s)
eitherElem x s = case isElem x s of
  No contra => Left (MkProvenElem x contra)
  Yes prf => Right (MkProvenElem x prf)

------------------------------------
-- Set proven and disproven elements
------------------------------------

public export
0 SetProvenElem : Set t a => t -> Type
SetProvenElem s = ProvenElem (SetPrf s)

public export
0 SetDisprovenElem : Set t a => t -> Type
SetDisprovenElem s = DisprovenElem (SetPrf s)
