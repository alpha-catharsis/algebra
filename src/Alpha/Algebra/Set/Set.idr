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
data Set : (a -> Type) -> Type -> Type where
  MkSet : {0 fpt : a -> Type} -> ((x : a) -> Dec (fpt x)) -> Set fpt a

setDec : Set fpt a -> ((x : a) -> Dec (fpt x))
setDec (MkSet f) = f

-----------------
-- Elem data type
-----------------

public export
data Elem : (x : a) -> (s : Set fpt a) -> Type where
  MkElem : (x : a) -> (s : Set fpt a) -> (prf : fpt x) -> Elem x s

public export
notElem : (x : a) -> (s : Set fpt a) -> (fpt x -> Void) -> Elem x s -> Void
notElem x s contra (MkElem x s prf) = contra prf

public export
isElem : (x : a) -> (s : Set fpt a) -> Dec (Elem x s)
isElem x (MkSet f) = case f x of
  Yes prf => Yes (MkElem x (MkSet f) prf)
  No contra => No (notElem x (MkSet f) contra)

public export
elem : (x : a) -> (s : Set fpt a) -> Bool
elem x s@(MkSet _) = isYes (isElem x s)
