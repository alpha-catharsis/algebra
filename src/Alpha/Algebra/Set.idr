module Alpha.Algebra.Set

-------------------
-- External imports
-------------------

import Data.Bool
import Decidable.Equality

-----------------------------------------
-- Set data type and associated functions
-----------------------------------------

public export
data Set : Type -> Type where
  MkSet : (a -> Bool) -> Set a

export
setFn : (s : Set a) -> (a -> Bool)
setFn (MkSet f) = f


---------------------------------------------
-- SetElem data type and 'contains' functions
---------------------------------------------

public export
data SetElem : (x : a) -> (s : Set a) -> Type where
  MkSetElem : (x : a) -> (s : Set a) -> setFn s x = True -> SetElem x s

notSetElemPrf : (x : a) -> (s : Set a) -> (setFn s x = True -> Void) ->
                SetElem x s -> Void
notSetElemPrf x s contra (MkSetElem x s eq) = contra eq

export
containsDec : (s : Set a) -> (x : a) -> Dec (SetElem x s)
containsDec s x = case decEq (setFn s x) True of
  Yes prf => Yes (MkSetElem x s prf)
  No contra => No (notSetElemPrf x s contra)

export
contains : (s : Set a) -> (x : a) -> Bool
contains s x = setFn s x


---------------
-- Trivial sets
----------------

-- empty set
export
emptySet : Set a
emptySet = MkSet (const False)

-- universe set
export
universeSet : Set a
universeSet = MkSet (const True)

-- singleton set
export
singletonSet : Eq a => (x : a) -> Set a
singletonSet x = MkSet (==x)


-------------------------------------------------
-- Set complement operation and associated proofs
-------------------------------------------------

-- complement operation
export
complement : Set a -> Set a
complement s = MkSet (not . setFn s)


-- complement not elem proof
boolFnTrueNotPrf : (x : a) -> (f : a -> Bool) -> f x = True ->
               not (f x) = True -> Void
boolFnTrueNotPrf x f eq = rewrite eq in uninhabited

export
complementNotElemPrf : (x : a) -> (s : Set a) -> SetElem x s ->
                       SetElem x (complement s) -> Void
complementNotElemPrf x s (MkSetElem _ _ eq) (MkSetElem _ _ neq) =
  boolFnTrueNotPrf x (setFn s) eq neq


-- complement elem proof
falseIsNotTrue : {x : Bool} -> x = False -> not x = True
falseIsNotTrue Refl = Refl

boolFnNotTruePrf : (x : a) -> (f : a -> Bool) -> (f x = True -> Void) ->
                   not (f x) = True
boolFnNotTruePrf x f contra = falseIsNotTrue (notTrueIsFalse contra)

notSetElemRevPrf : (x : a) -> (s : Set a) -> (SetElem x s -> Void) ->
                   setFn s x = True -> Void
notSetElemRevPrf x s contra eq = contra (MkSetElem x s eq)

export
complementElemPrf : (x : a) -> (s : Set a) -> (SetElem x s -> Void) ->
                    SetElem x (complement s)
complementElemPrf x s contra = MkSetElem x (complement s) (boolFnNotTruePrf x (setFn s) (notSetElemRevPrf x s contra))
