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

public export
universe : Set (\x => const () (the a x)) a
universe = MkSet (const (Yes ()))

public export
singleton : DecEq a => (x : a) -> Set (\y => x = y) a
singleton x = MkSet (\y => decEq x y)

revDecEq : DecEq a => {x : a} -> {y : a} -> (d : Dec (x = y)) -> Dec (Not (x = y))
revDecEq (No contra) = Yes contra
revDecEq (Yes prf) = No (\f => f prf)

public export
holed : DecEq a => (x : a) -> Set (\y => Not (x = y)) a
holed x = MkSet (\y => revDecEq (decEq x y))

public export
fnSet : (f : a -> Bool) -> Set (\x => f x = True) a
fnSet f = MkSet (\x => decEq (f x) True)


