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
0 Set : Type -> Type
Set a = a -> Type

public export
0 DecSet : Set a -> Type
DecSet s = (x : a) -> Dec (s x)

public export
isElem : (x : a) -> DecSet s -> Dec (s x)
isElem x ds = ds x

public export
elem : (x : a) -> {0 s : Set a} -> DecSet s -> Bool
elem x ds = isYes (isElem x ds)

--------------------------------
-- Proven and disproven elements
--------------------------------

public export
data ProvenElem : Set a -> Type where
  MkProvenElem : (x : a) -> (0 prf : s x) -> ProvenElem s

public export
provenElem : {0 s : Set a} -> ProvenElem s -> a
provenElem (MkProvenElem x _) = x

public export
0 elemPrf : (pe : ProvenElem s) -> s (provenElem pe)
elemPrf (MkProvenElem _ prf) = prf

public export
DisprovenElem : Set a -> Type
DisprovenElem s = ProvenElem (Not . s)

public export
projectElem : {0 s : Set a} -> {0 s' : Set a} -> (0 f : {x : a} -> s x -> s' x) -> ProvenElem s -> ProvenElem s'
projectElem f pe = MkProvenElem (provenElem pe) (f (elemPrf pe))

public export
EitherElem : Set a -> Type
EitherElem s = Either (DisprovenElem s) (ProvenElem s)

public export
eitherElem : (x : a) -> {0 s : Set a} -> DecSet s -> EitherElem s
eitherElem x ds = case isElem x ds of
  No contra => Left (MkProvenElem x contra)
  Yes prf => Right (MkProvenElem x prf)
