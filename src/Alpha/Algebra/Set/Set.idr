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
Set : Type -> Type
Set a = (fpt : (x : a) -> Type ** (x : a) -> Dec (fpt x))

public export
setPrf : Set a -> (x : a) -> Type
setPrf = fst

public export
setDec : (s : Set a) -> (x : a) -> Dec (setPrf s x)
setDec = snd

public export
isElem : (x : a) -> (s : Set a) -> Dec (setPrf s x)
isElem x s = snd s x

public export
elem : (x : a) -> (s : Set a) -> Bool
elem x s = isYes (isElem x s)

-----------------
-- Proven element
-----------------

public export
ProvenElem : {a : Type} -> (s : Set a) -> Type
ProvenElem s = (x : a ** setPrf s x)

public export
provenElem : {a : Type} -> {s : Set a} -> ProvenElem s -> a
provenElem p = fst p

public export
provenElemPrf : {a : Type} -> {s : Set a} -> (p : ProvenElem s) ->
                setPrf s (fst p)
provenElemPrf p = snd p

--------------------
-- Disproven element
--------------------

public export
DisprovenElem : {a : Type} -> (s : Set a) -> Type
DisprovenElem s = (x : a ** setPrf s x -> Void)

public export
disprovenElem : {a : Type} -> {s : Set a} -> DisprovenElem s -> a
disprovenElem d = fst d

public export
disprovenElemPrf : {a : Type} -> {s : Set a} -> (d : DisprovenElem s) ->
                   setPrf s (fst d) -> Void
disprovenElemPrf d = snd d

-------------------
-- Element checking
-------------------

public export
eitherSetPrf : (x : a) -> (s : Set a) ->
               Either (setPrf s x -> Void) (setPrf s x)
eitherSetPrf x s = case isElem x s of
  No contra => Left contra
  Yes prf => Right prf

public export
eitherProvenElem : (x : a) -> (s : Set a) ->
                   Either (DisprovenElem s) (ProvenElem s)
eitherProvenElem x s = case isElem x s of
  No contra => Left (x ** contra)
  Yes prf => Right (x ** prf)
