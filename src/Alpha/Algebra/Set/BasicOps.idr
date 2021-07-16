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
complement : Set fpt a -> Set (Not . fpt) a
complement (MkSet f) = MkSet (\x => decNot (f x))

public export
elemComplement : {0 fpt : a -> Type} -> {x : a} -> {s : Set fpt a} -> (Elem x s -> Void) -> Elem x (complement s)
elemComplement contra = MkElem x (complement s) (\y => contra (MkElem x s y))

public export
notElemComplement : {x : a} -> {s : Set fpt a} -> Elem x s -> Elem x (complement s) -> Void
notElemComplement (MkElem x s prf) = \(MkElem x _ contra) => contra prf

public export
elemComplement2 : {0 fpt : a -> Type} -> {x : a} -> {s : Set fpt a} -> Elem x s -> Elem x (complement (complement s))
elemComplement2 prf = elemComplement (notElemComplement prf)

public export
notElemComplement2 : {0 fpt : a -> Type} -> {x : a} -> {s : Set fpt a} -> (Elem x s -> Void) -> Elem x (complement (complement s)) -> Void
notElemComplement2 contra = notElemComplement (elemComplement contra)

------------
-- Set union
------------

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

public export
elemUnionCommutative : {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} -> Elem x (union ls rs) -> Elem x (union rs ls)
elemUnionCommutative (MkElem _ _ (Left lprf)) = MkElem _ _ (Right lprf)
elemUnionCommutative (MkElem _ _ (Right rprf)) = MkElem _ _ (Left rprf)

public export
notElemUnionCommutative : {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} -> (Elem x (union ls rs) -> Void) ->
                          Elem x (union rs ls) -> Void
notElemUnionCommutative contra = \(MkElem _ _ eprf) => case eprf of
  Left lprf => contra (MkElem _ _ (Right lprf))
  Right rprf => contra (MkElem _ _ (Left rprf))

public export
elemUnionIdempotent : {x : a} -> {s : Set lfpt a} -> Elem x (union s s) -> Elem x s
elemUnionIdempotent (MkElem _ _ (Left prf)) = MkElem _ _ prf
elemUnionIdempotent (MkElem _ _ (Right prf)) = MkElem _ _ prf

public export
notElemUnionIdempotent : {x : a} -> {s : Set lfpt a} -> (Elem x (union s s) -> Void) -> Elem x s -> Void
notElemUnionIdempotent contra = \(MkElem _ _ prf) => contra (MkElem _ _ (Left prf))

-------------------
-- Set intersection
-------------------

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
elemIntersectionCommutative : {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} ->
                              Elem x (intersection ls rs) -> Elem x (intersection rs ls)
elemIntersectionCommutative (MkElem _ _ (lprf, rprf)) = MkElem _ _ (rprf, lprf)

public export
notElemIntersectionCommutative : {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} ->
                                 (Elem x (intersection ls rs) -> Void) -> Elem x (intersection rs ls) -> Void
notElemIntersectionCommutative contra = \(MkElem _ _ pprf) => contra (MkElem _ _ (snd pprf, fst pprf))

public export
elemIntersectionIdempotent : {x : a} -> {s : Set lfpt a} -> Elem x (intersection s s) -> Elem x s
elemIntersectionIdempotent (MkElem _ _ (prf, _)) = MkElem _ _ prf

public export
notElemIntersectionIdempotent : {x : a} -> {s : Set lfpt a} -> (Elem x (intersection s s) -> Void) -> Elem x s -> Void
notElemIntersectionIdempotent contra = \(MkElem _ _ prf) => contra (MkElem _ _ (prf, prf))
