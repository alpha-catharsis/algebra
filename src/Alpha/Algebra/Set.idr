---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set

-------------------
-- External imports
-------------------

import Data.Bool
import Data.Contravariant
import Decidable.Decidable
import Decidable.Equality


---------------------------------------------------
-- Set data type and associated functions/instances
---------------------------------------------------

public export
data Set : Type -> Type where
  MkSet : (a -> Bool) -> Set a

public export
setFn : (s : Set a) -> (a -> Bool)
setFn (MkSet f) = f

export
Contravariant Set where
 contramap f (MkSet g) = MkSet (g . f)

---------------------------------------------
-- SetElem data type and 'contains' functions
---------------------------------------------

public export
data Elem : (x : a) -> (s : Set a) -> Type where
  MkElem : (x : a) -> (s : Set a) -> setFn s x = True -> Elem x s

notElem : (x : a) -> (s : Set a) -> (setFn s x = True -> Void) ->
          Elem x s -> Void
notElem x s contra (MkElem x s eq) = contra eq


public export
isElem : (x : a) -> (s : Set a) -> Dec (Elem x s)
isElem x s = case decEq (setFn s x) True of
  Yes prf => Yes (MkElem x s prf)
  No contra => No (notElem x s contra)

public export
elem : (x : a) -> (s : Set a) -> Bool
elem x s = setFn s x

------------
-- Empty set
------------

public export
empty : {a : Type} -> Set a
empty = MkSet (const False)

public export
Uninhabited (Elem x Alpha.Algebra.Set.empty) where
  uninhabited (MkElem _ _ _) impossible

---------------
-- Universe set
---------------

public export
universe : {a : Type} -> Set a
universe = MkSet (const True)

elemUniverse : {a : Type} -> {x : a} -> Elem x (universe {a})
elemUniverse = MkElem x (universe {a}) Refl

----------------
-- Singleton set
----------------

public export
singleton : DecEq a => (x : a) -> Set a
singleton x = MkSet (\y => isYes (decEq x y))

yesIsTrue : DecEq a => {x : a} -> isYes (decEq x x) = True
yesIsTrue with (decEq x x)
  yesIsTrue | Yes _ = Refl
  yesIsTrue | No contra = absurd (contra Refl)

elemSingleton : DecEq a => {x : a} -> Elem x (singleton x)
elemSingleton = MkElem _ _ (rewrite sym yesIsTrue in Refl)


-- notElemSingleton : DecEq a => {x : a} -> {y : a} ->
--                    {neq : (x = y) -> Void} ->
--                    Elem y (singleton x) -> Void
-- notElemSingleton with (decEq x y)
--   notElemSingleton | Yes prf = absurd (neq prf)
--   notElemSingleton | No contra = \(MkElem _ _ prf) => contra prf

-------------------------------------------------
-- Set complement operation and associated proofs
-------------------------------------------------

-- complement operation
-- public export
-- complement : Set a -> Set a
-- complement s = MkSet (not . setFn s)

-- complement not elem proof
-- boolFnTrueNot : (x : a) -> (f : a -> Bool) -> f x = True ->
--                not (f x) = True -> Void
-- boolFnTrueNot x f eq = rewrite eq in uninhabited

-- public export
-- complementNotElem : (x : a) -> (s : Set a) -> Elem x s ->
--                        Elem x (complement s) -> Void
-- complementNotElem x s (MkElem _ _ eq) (MkElem _ _ neq) =
--   boolFnTrueNot x (setFn s) eq neq

-- complement elem proof
-- falseIsNotTrue : {x : Bool} -> x = False -> not x = True
-- falseIsNotTrue Refl = Refl

-- boolFnNotTrue : (x : a) -> (f : a -> Bool) -> (f x = True -> Void) ->
--                    not (f x) = True
-- boolFnNotTrue x f contra = falseIsNotTrue (notTrueIsFalse contra)

-- notElemRev : (x : a) -> (s : Set a) -> (Elem x s -> Void) ->
--                    setFn s x = True -> Void
-- notElemRev x s contra eq = contra (MkElem x s eq)

-- public export
-- complementElem : (x : a) -> (s : Set a) -> (Elem x s -> Void) ->
--                     Elem x (complement s)
-- complementElem x s contra = MkElem x (complement s)
--                             (boolFnNotTrue x (setFn s) (notElemRev x s contra))

-- elem set or complement proof
-- public export elemSetOrComplement : (x : a) -> (s : Set a) -> Either
--                                     (Elem x (complement s)) (Elem x s)
-- elemSetOrComplement x s = case isElem x s of
--   No contra => Left (complementElem x s contra)
--   Yes prf   => Right prf


--------------------------------------------
-- Set union operation and associated proofs
--------------------------------------------

-- union operation
-- public export
-- union : Set a -> Set a -> Set a
