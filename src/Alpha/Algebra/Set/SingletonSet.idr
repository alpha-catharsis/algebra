---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.SingletonSet

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

----------------
-- Singleton set
----------------

public export
data SingletonSet : (x : a) -> Type where
  MkSingletonSet : (x : a) -> SingletonSet x

public export
data ElemSingletonSet : (x : a) -> (s : t) -> Type where
  MkElemSingletonSet : (y : a) -> (s : SingletonSet x) -> (y = x) ->
                       ElemSingletonSet y s

public export
notElemSingletonSet : {x : a} -> (y : a) -> (s : SingletonSet x) ->
                      ((y = x) -> Void) -> ElemSingletonSet y s -> Void
notElemSingletonSet y s contra (MkElemSingletonSet _ _ prf) = contra prf

export
{x : a} -> DecEq a => Set (SingletonSet x) a where
  SetElemPrf = ElemSingletonSet
  isElem y s = case decEq y x of
    Yes prf => Yes (MkElemSingletonSet y s prf)
    No contra => No (notElemSingletonSet y s contra)





-- export
-- singleton : DecEq a => (x : a) -> Set a
-- singleton x = MkSet (\y => x = y) (\y => decEq x y)

-- export
-- elemSingleton : DecEq a => {x : a} -> Elem x (singleton x)
-- elemSingleton = MkElem _ _ Refl

-- export
-- notElemSingleton : DecEq a => {y : a} -> {auto contra : (x = y) -> Void} ->
--                    Elem y (singleton x) -> Void
-- notElemSingleton (MkElem _ _ prf) = contra prf
