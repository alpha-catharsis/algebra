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
SetFpt : Type -> Type
SetFpt a = a -> Type

public export
Elem : a -> SetFpt a -> Type
Elem x fpt = fpt x

public export
NotElem : a -> SetFpt a -> Type
NotElem x fpt = Elem x fpt -> Void

public export
Set : {a : Type} -> SetFpt a -> Type
Set fpt = (x : a) -> Dec (fpt x)

public export
isElem : {fpt : SetFpt a} -> (x : a) -> Set fpt -> Dec (fpt x)
isElem x fn = fn x

public export
elem : {fpt : SetFpt a} -> (x : a) -> Set fpt -> Bool
elem x fn = isYes (isElem x fn)

