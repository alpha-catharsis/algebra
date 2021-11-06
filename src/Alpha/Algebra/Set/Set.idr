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
isElem : (x : a) -> (s : Set a) -> Dec (fst s x)
isElem x s = snd s x

public export
elem : (x : a) -> (s : Set a) -> Bool
elem x s = isYes (isElem x s)

public export
ProvenElem : {a : Type} -> (s : Set a) -> Type
ProvenElem s = (x : a ** fst s x)

public export
proven : {a : Type} -> {s : Set a} -> ProvenElem s -> a
proven p = fst p

public export
provenPrf : {a : Type} -> {s : Set a} -> (p : ProvenElem s) -> fst s (fst p)
provenPrf p = snd p

public export
maybeProven : (x : a) -> (s : Set a) -> Maybe (ProvenElem s)
maybeProven x s = case isElem x s of
  Yes prf => Just (x ** prf)
  No _ => Nothing
