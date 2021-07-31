---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.BasicOps

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
import Alpha.Decidable

-----------------
-- Set complement
-----------------

public export
data Complement : (t : Type) -> (a : Type) -> (Set t a) => Type where
  MkComplement : Set t a => t -> Complement t a

public export
complementSet : Set t a => Complement t a -> t
complementSet (MkComplement is) = is

public export
data ElemComplement : (Set t a) => a -> Complement t a -> Type where
  MkElemComplement : Set t a => (x : a) -> (is : t) ->
                     (SetElemPrf x is -> Void) ->
                     ElemComplement x (MkComplement is)

export
notElemComplement : Set t a => (x : a) -> (is : t) -> SetElemPrf x is ->
                    ElemComplement x (MkComplement is) -> Void
notElemComplement _ _ prf (MkElemComplement _ _ contra) = contra prf

public export
Set t a => Set (Complement t a) a where
  SetElemPrf = ElemComplement
  isElem x (MkComplement is) = case isElem x is of
    No contra => Yes (MkElemComplement x is contra)
    Yes prf => No  (notElemComplement x is prf)


-- export
-- elemComplement2 : {x : a} -> {s : Set a} ->
--                   Elem x s -> Elem x (complement (complement s))
-- elemComplement2 prf = elemComplement (notElemComplement prf)

-- export
-- notElemComplement2 : {x : a} -> {s : Set a} ->
--                      (Elem x s -> Void) ->
--                      Elem x (complement (complement s)) -> Void
-- notElemComplement2 contra = notElemComplement (elemComplement contra)

------------
-- Set union
------------

public export
data Union : (t : Type) -> (u : Type) -> (a : Type) ->
             (Set t a, Set u a) => Type where
  MkUnion : (Set t a, Set u a) => t -> u -> Union t u a

public export
unionLeftSet : (Set t a, Set u a) => Union t u a -> t
unionLeftSet (MkUnion lis _) = lis

public export
unionRightSet : (Set t a, Set u a) => Union t u a -> u
unionRightSet (MkUnion _ ris) = ris

public export
data ElemUnion : (Set t a, Set u a) => a -> Union t u a -> Type where
  MkElemUnion : (Set t a, Set u a) => (x : a) -> (lis : t) -> (ris : u) ->
                Either (SetElemPrf x lis) (SetElemPrf x ris) ->
                ElemUnion x (MkUnion lis ris)

export
notElemUnion : (Set t a, Set u a) => (x : a) -> (lis : t) -> (ris : u) ->
               (SetElemPrf x lis -> Void) -> (SetElemPrf x ris -> Void) ->
               ElemUnion x (MkUnion lis ris) -> Void
notElemUnion _ _ _ lcontra rcontra (MkElemUnion _ _ _ eprf) = case eprf of
  Left lprf => lcontra lprf
  Right rprf => rcontra rprf

public export
(Set t a, Set u a) => Set (Union t u a) a where
  SetElemPrf = ElemUnion
  isElem x (MkUnion lis ris) = case isElem x lis of
    Yes lprf => Yes (MkElemUnion _ _ _ (Left lprf))
    No lcontra => case isElem x ris of
      Yes rprf => Yes (MkElemUnion _ _ _ (Right rprf))
      No rcontra => No (notElemUnion _ _ _ lcontra rcontra)


-- export
-- elemUnionCommutative : {x : a} -> {ls : Set a} -> {rs : Set a} ->
--                        Elem x (union ls rs) -> Elem x (union rs ls)
-- elemUnionCommutative (MkElem _ _ (Left lprf)) = MkElem _ _ (Right lprf)
-- elemUnionCommutative (MkElem _ _ (Right rprf)) = MkElem _ _ (Left rprf)

-- export
-- notElemUnionCommutative : {x : a} -> {ls : Set a} -> {rs : Set a} ->
--                           (Elem x (union ls rs) -> Void) ->
--                           Elem x (union rs ls) -> Void
-- notElemUnionCommutative contra = \(MkElem _ _ eprf) => case eprf of
--   Left lprf => contra (MkElem _ _ (Right lprf))
--   Right rprf => contra (MkElem _ _ (Left rprf))

-- export
-- elemUnionIdempotent : {x : a} -> {s : Set a} -> Elem x (union s s) ->
--                       Elem x s
-- elemUnionIdempotent (MkElem _ _ (Left prf)) = MkElem _ _ prf
-- elemUnionIdempotent (MkElem _ _ (Right prf)) = MkElem _ _ prf

-- export
-- notElemUnionIdempotent : {x : a} -> {s : Set a} ->
--                          (Elem x (union s s) -> Void) -> Elem x s -> Void
-- notElemUnionIdempotent contra = \(MkElem _ _ prf) =>
--                                   contra (MkElem _ _ (Left prf))

-------------------
-- Set intersection
-------------------

public export
data Intersection : (t : Type) -> (u : Type) -> (a : Type) ->
                    (Set t a, Set u a) => Type where
  MkIntersection : (Set t a, Set u a) => t -> u -> Intersection t u a

public export
intersectionLeftSet : (Set t a, Set u a) => Intersection t u a -> t
intersectionLeftSet (MkIntersection lis _) = lis

public export
intersectionRightSet : (Set t a, Set u a) => Intersection t u a -> u
intersectionRightSet (MkIntersection _ ris) = ris

public export
data ElemIntersection : (Set t a, Set u a) =>  a -> Intersection t u a ->
                        Type where
  MkElemIntersection : (Set t a, Set u a) => (x : a) -> (lis : t) ->
                       (ris : u) -> (SetElemPrf x lis, SetElemPrf x ris) ->
                       ElemIntersection x (MkIntersection lis ris)

export
notElemIntersectionLeft : (Set t a, Set u a) => (x : a) -> (lis : t) ->
                          (ris : u) -> (SetElemPrf x lis -> Void) ->
                          ElemIntersection x (MkIntersection lis ris) -> Void
notElemIntersectionLeft _ _ _ lcontra (MkElemIntersection _ _ _ (lprf, _)) =
  lcontra lprf

export
notElemIntersectionRight : (Set t a, Set u a) => (x : a) -> (lis : t) ->
                           (ris : u) -> (SetElemPrf x ris -> Void) ->
                           ElemIntersection x (MkIntersection lis ris) -> Void
notElemIntersectionRight _ _ _ rcontra (MkElemIntersection _ _ _ (_, rprf)) =
  rcontra rprf

public export
(Set t a, Set u a) => Set (Intersection t u a) a where
  SetElemPrf = ElemIntersection
  isElem x (MkIntersection lis ris) = case isElem x lis of
    No lcontra => No (notElemIntersectionLeft _ _ _ lcontra)
    Yes lprf => case isElem x ris of
      No rcontra => No (notElemIntersectionRight _ _ _ rcontra)
      Yes rprf => Yes (MkElemIntersection _ _ _ (lprf, rprf))



-- export
-- elemIntersectionCommutative : {x : a} -> {ls : Set a} ->
--                               {rs : Set a} ->
--                               Elem x (intersection ls rs) ->
--                               Elem x (intersection rs ls)
-- elemIntersectionCommutative (MkElem _ _ (lprf, rprf)) = MkElem _ _ (rprf, lprf)

-- export
-- notElemIntersectionCommutative : {x : a} -> {ls : Set a} ->
--                                  {rs : Set a} ->
--                                  (Elem x (intersection ls rs) -> Void) ->
--                                  Elem x (intersection rs ls) -> Void
-- notElemIntersectionCommutative contra = \(MkElem _ _ pprf) =>
--     contra (MkElem _ _ (snd pprf, fst pprf))

-- export
-- elemIntersectionIdempotent : {x : a} -> {s : Set a} ->
--                              Elem x (intersection s s) -> Elem x s
-- elemIntersectionIdempotent (MkElem _ _ (prf, _)) = MkElem _ _ prf

-- export
-- notElemIntersectionIdempotent : {x : a} -> {s : Set a} ->
--                                 (Elem x (intersection s s) -> Void) ->
--                                 Elem x s -> Void
-- notElemIntersectionIdempotent contra = \(MkElem _ _ prf) =>
--                                          contra (MkElem _ _ (prf, prf))
