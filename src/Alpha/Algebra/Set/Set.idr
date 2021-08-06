---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Set

-------------------
-- External imports
-------------------

import Decidable.Decidable

------------------
-- Set definitions
------------------

public export
Set : Type -> Type
Set a = a -> Type

public export
Elem : a -> Set a -> Type
Elem x s = s x

public export
NotElem : a -> Set a -> Type
NotElem x s = Elem x s -> Void

public export
SetDec : {a : Type} -> Set a -> Type
SetDec s = (x : a) -> Dec (Elem x s)

public export
isElem : {s : Set a} -> (x : a) -> SetDec s -> Dec (Elem x s)
isElem x fn = fn x

public export
elem : {s : Set a} -> (x : a) -> SetDec s -> Bool
elem x fn = isYes (isElem x fn)

