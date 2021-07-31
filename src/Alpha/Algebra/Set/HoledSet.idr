---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.HoledSet

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
import Alpha.Decidable

------------
-- Holed set
------------

public export
data HoledSet : (x : a) -> Type where
  MkHoledSet : (x : a) -> HoledSet x

public export
data ElemHoledSet : (x : a) -> (s : t) -> Type where
  MkElemHoledSet : (y : a) -> (s : HoledSet x) -> (y = x -> Void) ->
                   ElemHoledSet y s

public export
notElemHoledSet : {x : a} -> (y : a) -> (s : HoledSet x) ->
                  y = x -> ElemHoledSet y s -> Void
notElemHoledSet y s prf (MkElemHoledSet _ _ contra) = contra prf

export
{x : a} -> DecEq a => Set (HoledSet x) a where
  SetElemPrf = ElemHoledSet
  isElem y s = case decEq y x of
    No contra => Yes (MkElemHoledSet y s contra)
    Yes prf => No (notElemHoledSet y s prf)


