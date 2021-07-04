module Alpha.Algebra.Set

import Data.List.Elem as LE
import Data.Vect.Elem as VE
import Data.Vect
import Decidable.Equality


-- Set interface and associated functions

interface Set s a p | s where
  isElemOfDec : DecEq a => (x : a) -> (t : s) -> Dec (p x t)

isElemOf : (DecEq a, Set s a p) => a -> s -> Bool
isElemOf x s = case isElemOfDec x s of
  Yes _ => True
  No _ => False


-- Empty set

data EmptySet = MkEmptySet

data EmptySetElemProof : a -> s -> Type

Uninhabited (EmptySetElemProof a s) where
  uninhabited _ impossible

Set EmptySet a EmptySetElemProof where
  isElemOfDec _ _ = No uninhabited


-- Universe set

data UniverseSet = MkUniverseSet

data UniverseSetElemProof : a -> s -> Type where
  MkUniverseSetElemProof : UniverseSetElemProof a s

Set UniverseSet a UniverseSetElemProof where
  isElemOfDec _ _ = Yes MkUniverseSetElemProof


-- Singleton set

record SingletonSet a where
  constructor MkSingletonSet
  element : a

Functor SingletonSet where
  map f (MkSingletonSet x) = MkSingletonSet (f x)

data SingletonSetElemProof : a -> SingletonSet a -> Type where
  MkSingletonSetElemProof :  (x : a) -> (s : SingletonSet a) ->
                             (x = element s) -> SingletonSetElemProof x s

singletonSetNoElemProof : (x : a) -> (s : SingletonSet a) ->
                          ((x = element s) -> Void) ->
                          SingletonSetElemProof x s -> Void
singletonSetNoElemProof x s prf (MkSingletonSetElemProof x s eq) = prf eq


Set (SingletonSet a) a SingletonSetElemProof where
  isElemOfDec x s = case decEq x (element s) of
    Yes prf => Yes (MkSingletonSetElemProof x s prf)
    No contra => No (singletonSetNoElemProof x s contra)


-- Function set

record FunSet a where
  constructor MkFunSet
  setFun : a -> Bool


data FunSetElemProof : a -> FunSet a -> Type where
  MkFunSetElemProof : (x : a) -> (s : FunSet a) ->
                  (setFun s x = True) -> FunSetElemProof x s

funSetNoElemProof : (x : a) -> (s : FunSet a) ->
                    ((setFun s x = True) -> Void) ->
                    FunSetElemProof x s -> Void
funSetNoElemProof x s prf (MkFunSetElemProof x s eq) = prf eq

Set (FunSet a) a FunSetElemProof where
  isElemOfDec x s = case decEq (setFun s x) True of
    Yes prf => Yes (MkFunSetElemProof x s prf)
    No contra => No (funSetNoElemProof x s contra)


-- List set

Set (List a) a LE.Elem where
  isElemOfDec = LE.isElem


-- Vec set

Set (Vect n a) a VE.Elem where
  isElemOfDec = VE.isElem















-- import Data.Contravariant
-- import Decidable.Equality

-- public export
-- data Set : Type -> Type  where
--   MkSet : {0 t : Type} -> (t -> Bool) -> Set t

-- public export
-- emptySet : Set t
-- emptySet = MkSet (const False)

-- public export
-- universeSet : Set t
-- universeSet = MkSet (const True)

-- public export
-- singletonSet : Eq t => t -> Set t
-- singletonSet x = MkSet (==x)

-- public export
-- setFunc : (s : Set t) -> (t -> Bool)
-- setFunc (MkSet f) = f

-- public export
-- data SetElem : (s : Set t) -> (x : t) -> Type where
--   InsideSet : (setFunc s x = True) -> SetElem s x

-- public export
-- insideSetPrf : SetElem s x -> (setFunc s x = True)
-- insideSetPrf (InsideSet prf) = prf

-- public export
-- containsDec : (s : Set t) -> (x : t) -> Dec (SetElem s x)
-- containsDec s x = case decEq (setFunc s x) True of
--   Yes prf => Yes (InsideSet prf)
--   No contra => No (contra . insideSetPrf)

-- public export
-- contains : (s : Set t) -> (x : t) -> Bool
-- contains s x = case containsDec s x of
--   Yes _ => True
--   No _ => False

-- public export
-- union : Set t -> Set t -> Set t
-- union (MkSet f) (MkSet g) = MkSet (\x => f x || g x)

-- public export
-- intersection : Set t -> Set t -> Set t
-- intersection (MkSet f) (MkSet g) = MkSet (\x => f x && g x)

-- public export
-- difference : Set t -> Set t -> Set t
-- difference (MkSet f) (MkSet g) = MkSet (\x => f x && (not (g x)))

-- public export
-- symdifference : Set t -> Set t -> Set t
-- symdifference (MkSet f) (MkSet g) = MkSet (\x => not (f x && g x))

-- public export
-- complement : Set t -> Set t
-- complement (MkSet f) = MkSet (\x => not (f x))

-- public export
-- Contravariant Set where
--   contramap f (MkSet g) = MkSet (g . f)
