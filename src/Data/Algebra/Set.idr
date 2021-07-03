module Data.Algebra.Set

import Decidable.Equality

public export
data Set : Type where
  MkSet : (a : Type) -> (a -> Bool) -> Set

public export
setType : Set -> Type
setType (MkSet a _)  = a

public export
setFunc : (s : Set) -> (setType s -> Bool)
setFunc (MkSet _ f) = f

public export
data SetElem : (s : Set) -> (x : setType s) -> Type where
  InsideSet : (setFunc s x = True) -> SetElem s x

public export
insideSetPrf : SetElem s x -> (setFunc s x = True)
insideSetPrf (InsideSet prf) = prf

public export
containsDec : (s : Set) -> (x : setType s) -> Dec (SetElem s x)
containsDec s x = case decEq (setFunc s x) True of
  Yes prf => Yes (InsideSet prf)
  No contra => No (contra . insideSetPrf)

public export
contains : (s : Set) -> (x : setType s) -> Bool
contains s x = case containsDec s x of
  Yes _ => True
  No _ => False


public export
data Tree : Type -> Type where
  MkLeaf : a -> Tree a
  MkBranch : Tree a -> Tree a -> Tree a

public export
treeSet : Type -> Set
treeSet x = MkSet (Tree x) (const True)
