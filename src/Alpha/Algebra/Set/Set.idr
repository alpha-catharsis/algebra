---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Set

-------------------
-- External imports
-------------------

import Decidable.Decidable

-----------------
-- Set definition
-----------------

public export
0 SetPrfTy : Type -> Type
SetPrfTy a = a -> Type

public export
Set : {a : Type} -> SetPrfTy a -> Type
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
ProvenElem : {a : Type} -> SetPrfTy a -> Type
ProvenElem pf = (x : a ** pf x)

public export
provenElem : {a : Type} -> {pty : SetPrfTy a} -> ProvenElem pty -> a
provenElem p = fst p

public export
provenElemPrf : (p : ProvenElem pty) -> pty (fst p)
provenElemPrf p = snd p

--------------------
-- Disproven element
--------------------

public export
DisprovenElem : {a : Type} -> SetPrfTy a -> Type
DisprovenElem pf = (x : a ** pf x -> Void)

public export
disprovenElem : {a : Type} -> {pty : SetPrfTy a} -> DisprovenElem pty -> a
disprovenElem d = fst d

public export
disprovenElemPrf : (d : DisprovenElem pty) -> pty (fst d) -> Void
disprovenElemPrf d = snd d

-------------------
-- Element checking
-------------------

public export
eitherSetPrf : (x : a) -> (s : Set {a} pty) -> Either (pty x -> Void) (pty x)
eitherSetPrf x s = case isElem x s of
  No contra => Left contra
  Yes prf => Right prf

public export
eitherProvenElem : (x : a) -> (s : Set {a} pty) ->
                   Either (DisprovenElem pty) (ProvenElem pty)
eitherProvenElem x s = case isElem x s of
  No contra => Left (x ** contra)
  Yes prf => Right (x ** prf)
