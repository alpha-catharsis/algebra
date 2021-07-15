---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set

-------------------
-- External imports
-------------------

import Data.Bool
import Data.Contravariant
import Data.List.Elem
import Decidable.Decidable
import Decidable.Equality

------------
-- Test area
------------

public export
data Set : (a -> Type) -> Type -> Type where
  MkSet : {0 fpt : a -> Type} -> ((x : a) -> Dec (fpt x)) -> Set fpt a

setDec : Set fpt a -> ((x : a) -> Dec (fpt x))
setDec (MkSet f) = f

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

public export
empty : Set (\x => const Void (the a x)) a
empty = MkSet (const (No id))

public export
Uninhabited (Elem x Alpha.Algebra.Set.empty) where
  uninhabited (MkElem _ _ _) impossible

public export
universe : Set (\x => const () (the a x)) a
universe = MkSet (const (Yes ()))

public export
elemUniverse : {x : a} -> Elem x Alpha.Algebra.Set.universe
elemUniverse = MkElem _ _ ()

public export
singleton : DecEq a => (x : a) -> Set (\y => x = y) a
singleton x = MkSet (\y => decEq x y)

public export
elemSingleton : DecEq a => {x : a} -> Elem x (singleton x)
elemSingleton = MkElem _ _ Refl

public export
notElemSingleton : DecEq a => {y : a} -> {auto contra : (x = y) -> Void} -> Elem y (singleton x) -> Void
notElemSingleton (MkElem _ _ prf) = contra prf

revDec : Dec prf -> Dec (Not prf)
revDec (No contra) = Yes contra
revDec (Yes prf) = No (\f => f prf)

public export
holed : DecEq a => (x : a) -> Set (\y => Not (x = y)) a
holed x = MkSet (\y => revDec (decEq x y))

public export
{x : a} -> DecEq a => Uninhabited (Elem x (holed x)) where
  uninhabited (MkElem _ _ contra) = contra Refl

public export
elemHoled : DecEq a => {y : a} -> {x : a} -> {auto contra : Not (x = y)} -> Elem y (holed x)
elemHoled = MkElem _ _ contra

public export
fnSet : (f : a -> Bool) -> Set (\x => f x = True) a
fnSet f = MkSet (\x => decEq (f x) True)

public export
elemFnSet : {x : a} -> {f : a -> Bool} -> {auto prf : f x = True} -> Elem x (fnSet f)
elemFnSet = MkElem _ _ prf

public export
notElemFnSet : {x : a} -> {f : a -> Bool} -> {auto contra : (f x = True) -> Void} -> Elem x (fnSet f) -> Void
notElemFnSet (MkElem _ _ prf) = contra prf

public export
complement : Set fpt a -> Set (Not . fpt) a
complement (MkSet f) = MkSet (\x => revDec (f x))

public export
elemComplement : {0 fpt : a -> Type} -> {x : a} -> {s : Set fpt a} -> (Elem x s -> Void) -> Elem x (complement s)
elemComplement contra = MkElem x (complement s) (\y => contra (MkElem x s y))

public export
notElemComplement : {x : a} -> {s : Set fpt a} -> Elem x s -> Elem x (complement s) -> Void
notElemComplement (MkElem x s prf) = \(MkElem x _ contra) => contra prf

decOr : Dec lprf -> Dec rprf -> Dec (Either lprf rprf)
decOr ldec rdec = case ldec of
  Yes lprf => Yes (Left lprf)
  No lcontra => case rdec of
    Yes rprf => Yes (Right rprf)
    No rcontra => No (\ex => case ex of
      Left lx => lcontra lx
      Right rx => rcontra rx)

public export
union : Set lfpt a -> Set rfpt a -> Set (\x => Either (lfpt x) (rfpt x)) a
union (MkSet lf) (MkSet rf) = MkSet (\x => decOr (lf x) (rf x))

public export
elemUnionLeft : {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} -> Elem x ls -> Elem x (union ls rs)
elemUnionLeft (MkElem _ _ prf) = MkElem _ _ (Left prf)

public export
elemUnionRight : {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} -> Elem x rs -> Elem x (union ls rs)
elemUnionRight (MkElem _ _ prf) = MkElem _ _ (Right prf)

public export
notElemUnion : {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} -> (Elem x ls -> Void) ->
               (Elem x rs -> Void) -> Elem x (union ls rs) -> Void
notElemUnion lcontra rcontra = \(MkElem _ _ eprf) => case eprf of
                                                       Left lprf => lcontra (MkElem _ _ lprf)
                                                       Right rprf => rcontra (MkElem _ _ rprf)

decAnd : Dec lprf -> Dec rprf -> Dec (lprf, rprf)
decAnd ldec rdec = case ldec of
  No lcontra => No (\x => lcontra (fst x))
  Yes lprf => case rdec of
    No rcontra => No (\x => rcontra (snd x))
    Yes rprf => Yes (lprf, rprf)

public export
intersection : Set lfpt a -> Set rfpt a -> Set (\x => (lfpt x, rfpt x)) a
intersection (MkSet lf) (MkSet rf) = MkSet (\x => decAnd (lf x) (rf x))

public export
elemIntersection : {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} ->
                   Elem x ls -> Elem x rs -> Elem x (intersection ls rs)
elemIntersection (MkElem _ _ lprf) (MkElem _ _ rprf) = MkElem _ _ (lprf, rprf)

public export
notElemIntersectionLeft : {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} -> (Elem x ls -> Void) -> Elem x (intersection ls rs) -> Void
notElemIntersectionLeft lcontra = \(MkElem _ _ (lprf, _)) => lcontra (MkElem _ _ lprf)

public export
notElemIntersectionRight : {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} -> (Elem x rs -> Void) -> Elem x (intersection ls rs) -> Void
notElemIntersectionRight rcontra = \(MkElem _ _ (_, rprf)) => rcontra (MkElem _ _ rprf)

public export
difference : Set lfpt a -> Set rfpt a -> Set (\x => (lfpt x, Not (rfpt x))) a
difference ls rs = intersection ls (complement rs)

elemDifference : {0 rfpt : a -> Type} -> {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} -> Elem x ls -> (Elem x rs -> Void) -> Elem x (difference ls rs)
elemDifference lprf rcontra = elemIntersection lprf (elemComplement rcontra)

public export
notElemDifferenceLeft : {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} -> (Elem x ls -> Void) -> Elem x (difference ls rs) -> Void
notElemDifferenceLeft lcontra = notElemIntersectionLeft lcontra

public export
notElemDifferenceRight : {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} -> Elem x rs -> Elem x (difference ls rs) -> Void
notElemDifferenceRight rprf = notElemIntersectionRight (notElemComplement rprf)

public export
symDifference : {lfpt : a -> Type} -> Set lfpt a -> Set rfpt a -> Set (\x => Either (lfpt x, Not (rfpt x)) (rfpt x , Not (lfpt x))) a
symDifference ls rs = union (difference ls rs) (difference rs ls)

elemSymDifferenceLeft : {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} -> Elem x ls -> (Elem x rs -> Void) ->
                        Elem x (symDifference ls rs)
elemSymDifferenceLeft lprf rcontra = elemUnionLeft (elemDifference lprf rcontra)

elemSymDifferenceRight : {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} -> (Elem x ls -> Void) -> Elem x rs ->
                        Elem x (symDifference ls rs)
elemSymDifferenceRight lcontra rprf = elemUnionRight (elemDifference rprf lcontra)

notElemSymDifferenceBoth : {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} -> Elem x ls -> Elem x rs ->
                           Elem x (symDifference ls rs) -> Void
notElemSymDifferenceBoth lprf rprf = notElemUnion (notElemDifferenceRight rprf) (notElemDifferenceRight lprf)

notElemSymDifferenceBothNot : {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} -> (Elem x ls -> Void) -> (Elem x rs -> Void) ->
                              Elem x (symDifference ls rs) -> Void
notElemSymDifferenceBothNot lprf rprf = notElemUnion (notElemDifferenceLeft lprf) (notElemDifferenceLeft rprf)

public export
product : Set lfpt a -> Set rfpt b -> Set (\x => (lfpt (Builtin.fst x), rfpt (Builtin.snd x))) (a, b)
product (MkSet lf) (MkSet rf) = MkSet (\x => decAnd (lf (fst x)) (rf (snd x)))

elemProduct : {ls : Set lfpt a} -> {rs : Set rfpt b} -> Elem x ls -> Elem y rs -> Elem (x, y) (product ls rs)
elemProduct (MkElem _ _ lprf) (MkElem _ _ rprf) = MkElem _ _ (lprf, rprf)


notElemProductLeft : {x : a} -> {y : b} -> {lfpt : a -> Type} -> {rfpt : a -> Type} -> {ls : Set lfpt a} -> {rs : Set rfpt b} ->
                     (Elem x ls -> Void) -> Elem (x, y) (product ls rs) -> Void
notElemProductLeft lcontra = \(MkElem _ _ pprf) => lcontra (MkElem _ _ (fst pprf))

notElemProductRight : {x : a} -> {y : b} -> {lfpt : a -> Type} -> {rfpt : a -> Type} -> {ls : Set lfpt a} -> {rs : Set rfpt b} ->
                      (Elem y rs -> Void) -> Elem (x, y) (product ls rs) -> Void
notElemProductRight rcontra = \(MkElem _ _ pprf) => rcontra (MkElem _ _ (snd pprf))

public export
coproduct : Set lfpt a -> Set rfpt b -> Set (\ex => either lfpt rfpt ex) (Either a b)
coproduct (MkSet lf) (MkSet rf) = MkSet (\ex => case ex of
                                                  Left lx => lf lx
                                                  Right rx => rf rx)

elemCoproductLeft : {x : a} -> {y : b} -> {lfpt : a -> Type} -> {rfpt : b -> Type} -> {ls : Set lfpt a} -> {rs : Set rfpt b} ->
                    Elem x ls -> Elem (Left x) (coproduct ls rs)
elemCoproductLeft (MkElem _ _ lprf) = MkElem _ _ lprf

elemCoproductRight : {x : a} -> {y : b} -> {lfpt : a -> Type} -> {rfpt : b -> Type} -> {ls : Set lfpt a} -> {rs : Set rfpt b} ->
                     Elem y rs -> Elem (Right y) (coproduct ls rs)
elemCoproductRight (MkElem _ _ rprf) = MkElem _ _ rprf
