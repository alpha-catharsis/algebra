---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.ProductOps

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.BasicOps
import Alpha.Algebra.Set.DerivedOps
import Alpha.Algebra.Set.Set
import Alpha.Decidable

--------------
-- Set product
--------------

public export
data Product : (t : Type) -> (u : Type) -> (a : Type) -> (b : Type) ->
               (Set t a, Set u b) => Type where
  MkProduct : (Set t a, Set u b) => t -> u -> Product t u a b

public export
productLeftSet : (Set t a, Set u b) => Product t u a b -> t
productLeftSet (MkProduct lis _) = lis

public export
productRightSet : (Set t a, Set u b) => Product t u a b -> u
productRightSet (MkProduct _ ris) = ris

public export
data ElemProduct : (Set t a, Set u b) => (a, b) -> Product t u a b ->
                   Type where
  MkElemProduct : (Set t a, Set u b) => (p : (a, b)) -> (lis : t) ->
                  (ris : u) ->
                  (SetElemPrf (fst p) lis, SetElemPrf (snd p) ris) ->
                  ElemProduct p (MkProduct lis ris)

export
notElemProductLeft : (Set t a, Set u b) => (x : a) -> (y : b) -> (lis : t) ->
                     (ris : u) -> (SetElemPrf x lis -> Void) ->
                     ElemProduct (x, y) (MkProduct lis ris) -> Void
notElemProductLeft _ _ _ _ lcontra (MkElemProduct _ _ _ (lprf, _)) =
  lcontra lprf

export
notElemProductRight : (Set t a, Set u b) => (x : a) -> (y : b) -> (lis : t) ->
                      (ris : u) -> (SetElemPrf y ris -> Void) ->
                      ElemProduct (x, y) (MkProduct lis ris) -> Void
notElemProductRight _ _ _ _ rcontra (MkElemProduct _ _ _ (_, rprf)) =
  rcontra rprf

public export
(Set t a, Set u b) => Set (Product t u a b) (a, b) where
  SetElemPrf = ElemProduct
  isElem (x, y) (MkProduct lis ris) = case isElem x lis of
    No lcontra => No (notElemProductLeft _ _ _ _ lcontra)
    Yes lprf => case isElem y ris of
      No rcontra => No (notElemProductRight _ _ _ _ rcontra)
      Yes rprf => Yes (MkElemProduct _ _ _ (lprf, rprf))

----------------
-- Set coproduct
----------------

public export
data Coproduct : (t : Type) -> (u : Type) -> (a : Type) -> (b : Type) ->
                 (Set t a, Set u b) => Type where
  MkCoproduct : (Set t a, Set u b) => t -> u -> Coproduct t u a b

public export
coproductLeftSet : (Set t a, Set u b) => Coproduct t u a b -> t
coproductLeftSet (MkCoproduct lis _) = lis

public export
coproductRightSet : (Set t a, Set u b) => Coproduct t u a b -> u
coproductRightSet (MkCoproduct _ ris) = ris

public export
data ElemCoproduct : (Set t a, Set u b) => Either a b -> Coproduct t u a b ->
                     Type where
  MkElemCoproduct : (Set t a, Set u b) => (e : Either a b) -> (lis : t) ->
                    (ris : u) -> (case e of
                                    Left x => SetElemPrf x lis
                                    Right y => SetElemPrf y ris) ->
                                    ElemCoproduct e (MkCoproduct lis ris)

export
notElemCoproductLeft : (Set t a, Set u b) => (x : a) -> (lis : t) ->
                       {ris : u}  -> (SetElemPrf x lis -> Void) ->
                       ElemCoproduct (Left x) (MkCoproduct lis ris) -> Void
notElemCoproductLeft  _ _ lcontra (MkElemCoproduct _ _ _ lprf) =
    lcontra lprf

export
notElemCoproductRight : (Set t a, Set u b) => (y : b) -> (ris : u) ->
                        {lis : t}  -> (SetElemPrf y ris -> Void) ->
                        ElemCoproduct (Right y) (MkCoproduct lis ris) -> Void
notElemCoproductRight  _ _ rcontra (MkElemCoproduct _ _ _ rprf) =
  rcontra rprf

public export
(Set t a, Set u b) => Set (Coproduct t u a b) (Either a b) where
  SetElemPrf = ElemCoproduct
  isElem (Left x) (MkCoproduct lis _) = case isElem x lis of
    No lcontra => No (notElemCoproductLeft x lis lcontra)
    Yes lprf => Yes (MkElemCoproduct (Left x) lis _ lprf)
  isElem (Right y) (MkCoproduct _ ris) = case isElem y ris of
    No rcontra => No (notElemCoproductRight y ris rcontra)
    Yes rprf => Yes (MkElemCoproduct (Right y) _ ris rprf)
