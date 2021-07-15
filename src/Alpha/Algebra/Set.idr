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

------------
-- Test area
------------

public export
data Set : (a -> Type) -> Type -> Type where
  MkSet : {0 fpt : a -> Type} -> ((x : a) -> Dec (fpt x)) -> Set fpt a

public export
isElem : (x : a) -> Set fpt a -> Dec (fpt x)
isElem x (MkSet f) = f x

public export
elem : (x : a) -> (s : Set fpt a) -> Bool
elem x s@(MkSet _) = isYes (isElem x s)

public export
empty : Set (\x => const Void (the a x)) a
empty = MkSet (const (No id))

-- isElemEmpty : isElem _ Alpha.Algebra.Set.empty = No Prelude.Basics.id
-- isElemEmpty = Refl

public export
universe : Set (\x => const () (the a x)) a
universe = MkSet (const (Yes ()))

-- isElemUniverse : isElem _ Alpha.Algebra.Set.universe = Yes ()
-- isElemUniverse = Refl

public export
singleton : DecEq a => (x : a) -> Set (\y => x = y) a
singleton x = MkSet (\y => decEq x y)

revDec : Dec prf -> Dec (Not prf)
revDec (No contra) = Yes contra
revDec (Yes prf) = No (\f => f prf)

public export
holed : DecEq a => (x : a) -> Set (\y => Not (x = y)) a
holed x = MkSet (\y => revDec (decEq x y))

public export
fnSet : (f : a -> Bool) -> Set (\x => f x = True) a
fnSet f = MkSet (\x => decEq (f x) True)

public export
complement : Set fpt a -> Set (Not . fpt) a
complement (MkSet f) = MkSet (\x => revDec (f x))

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
difference : Set lfpt a -> Set rfpt a -> Set (\x => (lfpt x, Not (rfpt x))) a
difference ls rs = intersection ls (complement rs)

public export
symDifference : Set lfpt a -> Set rfpt a -> Set (\x => Either (lfpt x, Not (rfpt x)) (rfpt x , Not (lfpt x))) a
symDifference ls rs = union (difference ls rs) (difference rs ls)

public export
product : Set lfpt a -> Set rfpt b -> Set (\x => (lfpt (Builtin.fst x), rfpt (Builtin.snd x))) (a, b)
product (MkSet lf) (MkSet rf) = MkSet (\x => decAnd (lf (fst x)) (rf (snd x)))

public export
coproduct : Set lfpt a -> Set rfpt b -> Set (\ex => either lfpt rfpt ex) (Either a b)
coproduct (MkSet lf) (MkSet rf) = MkSet (\ex => case ex of
                                                  Left lx => lf lx
                                                  Right rx => rf rx)
