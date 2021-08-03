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
complement : Set a -> Set a
complement s = MkSet (Not . setFpt s) (\x => decNot (setDec s x))

export
elemComplement : {x : a} -> {s : Set a} ->
                 (Elem x s -> Void) -> Elem x (complement s)
elemComplement contra = MkElem x (complement s) (\y => contra (MkElem x s y))

export
notElemComplement : {x : a} -> {s : Set a} -> Elem x s ->
                    Elem x (complement s) -> Void
notElemComplement (MkElem x s prf) = \(MkElem x _ contra) => contra prf

export
elemComplement2 : {x : a} -> {s : Set a} ->
                  Elem x s -> Elem x (complement (complement s))
elemComplement2 prf = elemComplement (notElemComplement prf)

export
notElemComplement2 : {x : a} -> {s : Set a} ->
                     (Elem x s -> Void) ->
                     Elem x (complement (complement s)) -> Void
notElemComplement2 contra = notElemComplement (elemComplement contra)

------------
-- Set union
------------

public export
union : Set a -> Set a -> Set a
union ls rs = MkSet (\x => Either (setFpt ls x) (setFpt rs x))
              (\x => decOr (setDec ls x) (setDec rs x))

export
elemUnionLeft : {ls : Set a} -> {rs : Set a} ->
                Elem x ls -> Elem x (union ls rs)
elemUnionLeft (MkElem _ _ prf) = MkElem _ _ (Left prf)

export
elemUnionRight : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                 Elem x rs -> Elem x (union ls rs)
elemUnionRight (MkElem _ _ prf) = MkElem _ _ (Right prf)

export
notElemUnion : {x : a} -> {ls : Set a} -> {rs : Set a} ->
               (Elem x ls -> Void) -> (Elem x rs -> Void) ->
               Elem x (union ls rs) -> Void
notElemUnion lcontra rcontra = \(MkElem _ _ eprf) => case eprf of
  Left lprf => lcontra (MkElem _ _ lprf)
  Right rprf => rcontra (MkElem _ _ rprf)

export
elemUnionCommutative : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                       Elem x (union ls rs) -> Elem x (union rs ls)
elemUnionCommutative (MkElem _ _ (Left lprf)) = MkElem _ _ (Right lprf)
elemUnionCommutative (MkElem _ _ (Right rprf)) = MkElem _ _ (Left rprf)

export
notElemUnionCommutative : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                          (Elem x (union ls rs) -> Void) ->
                          Elem x (union rs ls) -> Void
notElemUnionCommutative contra = \(MkElem _ _ eprf) => case eprf of
  Left lprf => contra (MkElem _ _ (Right lprf))
  Right rprf => contra (MkElem _ _ (Left rprf))

export
elemUnionIdempotent : {x : a} -> {s : Set a} -> Elem x (union s s) ->
                      Elem x s
elemUnionIdempotent (MkElem _ _ (Left prf)) = MkElem _ _ prf
elemUnionIdempotent (MkElem _ _ (Right prf)) = MkElem _ _ prf

export
notElemUnionIdempotent : {x : a} -> {s : Set a} ->
                         (Elem x (union s s) -> Void) -> Elem x s -> Void
notElemUnionIdempotent contra = \(MkElem _ _ prf) =>
                                  contra (MkElem _ _ (Left prf))

-------------------
-- Set intersection
-------------------

public export
intersection : Set a -> Set a -> Set a
intersection ls rs = MkSet (\x => (setFpt ls x, setFpt rs x))
                     (\x => decAnd (setDec ls x) (setDec rs x))

export
elemIntersection : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                   Elem x ls -> Elem x rs -> Elem x (intersection ls rs)
elemIntersection (MkElem _ _ lprf) (MkElem _ _ rprf) = MkElem _ _ (lprf, rprf)

export
notElemIntersectionLeft : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                          (Elem x ls -> Void) ->
                          Elem x (intersection ls rs) -> Void
notElemIntersectionLeft lcontra = \(MkElem _ _ (lprf, _)) =>
                                    lcontra (MkElem _ _ lprf)

export
notElemIntersectionRight : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                           (Elem x rs -> Void) ->
                           Elem x (intersection ls rs) -> Void
notElemIntersectionRight rcontra = \(MkElem _ _ (_, rprf)) =>
                                     rcontra (MkElem _ _ rprf)

export
elemIntersectionCommutative : {x : a} -> {ls : Set a} ->
                              {rs : Set a} ->
                              Elem x (intersection ls rs) ->
                              Elem x (intersection rs ls)
elemIntersectionCommutative (MkElem _ _ (lprf, rprf)) = MkElem _ _ (rprf, lprf)

export
notElemIntersectionCommutative : {x : a} -> {ls : Set a} ->
                                 {rs : Set a} ->
                                 (Elem x (intersection ls rs) -> Void) ->
                                 Elem x (intersection rs ls) -> Void
notElemIntersectionCommutative contra = \(MkElem _ _ pprf) =>
    contra (MkElem _ _ (snd pprf, fst pprf))

export
elemIntersectionIdempotent : {x : a} -> {s : Set a} ->
                             Elem x (intersection s s) -> Elem x s
elemIntersectionIdempotent (MkElem _ _ (prf, _)) = MkElem _ _ prf

export
notElemIntersectionIdempotent : {x : a} -> {s : Set a} ->
                                (Elem x (intersection s s) -> Void) ->
                                Elem x s -> Void
notElemIntersectionIdempotent contra = \(MkElem _ _ prf) =>
                                         contra (MkElem _ _ (prf, prf))

