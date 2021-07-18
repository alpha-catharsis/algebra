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
  MkSet : (fpt : a -> Type) -> ((x : a) -> Dec (fpt x)) -> Set a

public export
setFpt : Set a -> (a -> Type)
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
