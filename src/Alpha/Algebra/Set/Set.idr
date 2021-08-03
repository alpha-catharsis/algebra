---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Set

-------------------
-- External imports
-------------------

import Data.Bool
import Decidable.Decidable

----------------
-- set data type
----------------

public export
data Set : Type -> Type where
  MkSet : (0 fpt : a -> Type) -> ((x : a) -> Dec (fpt x)) -> Set a

public export
0 setFpt : Set a -> (a -> Type)
setFpt (MkSet fpt _) = fpt

public export
setDec : (s : Set a) -> ((x : a) -> Dec (setFpt s x))
setDec (MkSet _ f) = f

-----------------
-- Elem data type
-----------------

public export
data Elem : (x : a) -> (s : Set a) -> Type where
  MkElem : (x : a) -> (s : Set a) -> (prf : setFpt s x) -> Elem x s

public export
elemVal : {0 x : a} -> {0 s : Set a} -> Elem x s -> a
elemVal (MkElem x _ _) = x

public export
elemSet : {0 x : a} -> {0 s : Set a} -> Elem x s -> Set a
elemSet (MkElem _ s _) = s

public export
elemPrf : {0 x : a} -> {0 s : Set a} -> Elem x s -> setFpt s x
elemPrf (MkElem _ _ prf) = prf

export
notElem : (x : a) -> (s : Set a) -> (setFpt s x -> Void) -> Elem x s -> Void
notElem _ _ contra (MkElem _ _ prf) = contra prf

export
isElem : (x : a) -> (s : Set a) -> Dec (Elem x s)
isElem x s = case setDec s x of
  Yes prf => Yes (MkElem x s prf)
  No contra => No (notElem x s contra)

export
elem : (x : a) -> (s : Set a) -> Bool
elem x s = isYes (isElem x s)
