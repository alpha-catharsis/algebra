module Alpha.Algebra.Set

import Data.Contravariant
import Decidable.Equality

public export
data Set : Type -> Type  where
  MkSet : {0 t : Type} -> (t -> Bool) -> Set t

public export
emptySet : Set t
emptySet = MkSet (const False)

public export
universeSet : Set t
universeSet = MkSet (const True)

public export
setFunc : (s : Set t) -> (t -> Bool)
setFunc (MkSet f) = f

public export
data SetElem : (s : Set t) -> (x : t) -> Type where
  InsideSet : (setFunc s x = True) -> SetElem s x

public export
insideSetPrf : SetElem s x -> (setFunc s x = True)
insideSetPrf (InsideSet prf) = prf

public export
containsDec : (s : Set t) -> (x : t) -> Dec (SetElem s x)
containsDec s x = case decEq (setFunc s x) True of
  Yes prf => Yes (InsideSet prf)
  No contra => No (contra . insideSetPrf)

public export
contains : (s : Set t) -> (x : t) -> Bool
contains s x = case containsDec s x of
  Yes _ => True
  No _ => False

public export
union : Set t -> Set t -> Set t
union (MkSet f) (MkSet g) = MkSet (\x => f x || g x)

public export
intersection : Set t -> Set t -> Set t
intersection (MkSet f) (MkSet g) = MkSet (\x => f x && g x)

public export
difference : Set t -> Set t -> Set t
difference (MkSet f) (MkSet g) = MkSet (\x => f x && (not (g x)))

public export
symdifference : Set t -> Set t -> Set t
symdifference (MkSet f) (MkSet g) = MkSet (\x => not (f x && g x))

public export
complement : Set t -> Set t
complement (MkSet f) = MkSet (\x => not (f x))

public export
Contravariant Set where
  contramap f (MkSet g) = MkSet (g . f)
