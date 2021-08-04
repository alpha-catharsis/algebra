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
SetPrf : SetFpt a -> a -> Type
SetPrf fpt x = fpt x

public export
SetContra : SetFpt a -> a -> Type
SetContra fpt x = SetPrf fpt x -> Void

public export
SetFn : {a : Type} -> SetFpt a -> Type
SetFn fpt = (x : a) -> Dec (fpt x)

public export
isElem : {fpt : SetFpt a} -> (x : a) -> SetFn fpt -> Dec (fpt x)
isElem x fn = fn x

public export
elem : {fpt : SetFpt a} -> (x : a) -> SetFn fpt -> Bool
elem x fn = isYes (isElem x fn)

