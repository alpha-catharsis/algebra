---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.PropSet

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

------------------
-- Proposition set
------------------

public export
data PropSet : Type -> Type where
  MkPropSet : (a -> Bool) -> PropSet a

propSetFn : PropSet a -> (a -> Bool)
propSetFn (MkPropSet f) = f

public export
data ElemPropSet : (x : a) -> (s : t) -> Type where
  MkElemPropSet : (x : a) -> (s : PropSet a) -> propSetFn s x = True ->
                  ElemPropSet x s

public export
notElemPropSet : (x : a) -> (s : PropSet a) ->
                 (propSetFn s x = True -> Void) -> ElemPropSet x s -> Void
notElemPropSet x s contra (MkElemPropSet _ _ prf) = contra prf

export
Set (PropSet a) a where
  SetElemPrf = ElemPropSet
  isElem x s = case decEq (propSetFn s x) True of
    Yes prf => Yes (MkElemPropSet _ _ prf)
    No contra => No (notElemPropSet _ _ contra)
