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
0 Set : SetPrfTy a -> Type
Set pf = (x : a) -> Dec (pf x)

public export
isElem : (x : a) -> (s : Set pty) -> Dec (pty x)
isElem x s = s x

public export
elem : (x : a) -> (s : Set {a} pty) -> Bool
elem x s = isYes (isElem x s)

-----------------
-- Proven element
-----------------

public export
0 ProvenElem : {a : Type} -> SetPrfTy a -> Type
ProvenElem pf = Subset a pf

public export
provenElem : {0 pty : SetPrfTy a} -> ProvenElem pty -> a
provenElem p = fst p

public export
0 provenElemPrf : (p : ProvenElem pty) -> pty (fst p)
provenElemPrf p = snd p

--------------------
-- Disproven element
--------------------

public export
0 DisprovenElem : {a : Type} -> SetPrfTy a -> Type
DisprovenElem pf = Subset a (\x => pf x -> Void)

public export
disprovenElem : {0 pty : SetPrfTy a} -> DisprovenElem pty -> a
disprovenElem d = fst d

public export
0 disprovenElemPrf : (d : DisprovenElem pty) -> pty (fst d) -> Void
disprovenElemPrf d = snd d

-------------------
-- Element checking
-------------------

public export
eitherSetPrf : (x : a) -> Set pty -> Either (pty x -> Void) (pty x)
eitherSetPrf x s = case isElem x s of
  No contra => Left contra
  Yes prf => Right prf

public export
eitherProvenElem : (x : a) -> Set {a} pty ->
                   Either (DisprovenElem pty) (ProvenElem pty)
eitherProvenElem x s = case isElem x s of
  No contra => Left (Element x contra)
  Yes prf => Right (Element x prf)
