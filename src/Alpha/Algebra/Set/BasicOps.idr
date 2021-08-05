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
ComplementFpt : SetFpt a -> SetFpt a
ComplementFpt fpt = Not . fpt

public export
complement : Set fpt -> Set (ComplementFpt fpt)
complement f x = decNot (f x)

export
elemComplement : NotElem x fpt -> Elem x (ComplementFpt fpt)
elemComplement = id

export
notElemComplement : Elem x fpt -> NotElem x (ComplementFpt fpt)
notElemComplement prf cprf = cprf prf

elemComplement2 : {fpt : SetFpt a} -> Elem x fpt ->
                  Elem x (ComplementFpt (ComplementFpt fpt))
elemComplement2 prf f = f prf

export
notElemComplement2 : (NotElem x fpt) ->
                     NotElem x (ComplementFpt (ComplementFpt fpt))
notElemComplement2 contra f = f contra

------------
-- Set union
------------

public export
UnionFpt : SetFpt a -> SetFpt a -> SetFpt a
UnionFpt lfpt rfpt x = Either (lfpt x) (rfpt x)

public export
union : Set lfpt -> Set rfpt -> Set (UnionFpt lfpt rfpt)
union lf rf x = decOr (lf x) (rf x)

export
elemUnionLeft : Elem x lfpt -> Elem x (UnionFpt lfpt _)
elemUnionLeft prf = Left prf

export
elemUnionRight : Elem x rfpt -> Elem x (UnionFpt _ rfpt)
elemUnionRight prf = Right prf

export
notElemUnion : NotElem x lfpt -> NotElem x rfpt ->
               NotElem x (UnionFpt lfpt rfpt)
notElemUnion lcontra rcontra = either lcontra rcontra

export
elemUnionCommutative : Elem x (UnionFpt lfpt rfpt) ->
                       Elem x (UnionFpt rfpt lfpt)
elemUnionCommutative eprf = case eprf of
  Left lprf => Right lprf
  Right rprf => Left rprf

export
notElemUnionCommutative : NotElem x (UnionFpt lfpt rfpt) ->
                          NotElem x (UnionFpt rfpt lfpt)
notElemUnionCommutative contra pprf = case pprf of
  Left lprf => contra (Right lprf)
  Right rprf => contra (Left rprf)

export
elemUnionIdempotent : Elem x (UnionFpt fpt fpt) -> Elem x fpt
elemUnionIdempotent eprf = case eprf of
  Left lprf => lprf
  Right rprf => rprf

export
notElemUnionIdempotent : NotElem x (UnionFpt fpt fpt) -> NotElem x fpt
notElemUnionIdempotent contra prf = contra (Left prf)

-------------------
-- Set intersection
-------------------

public export
IntersectionFpt : SetFpt a -> SetFpt a -> SetFpt a
IntersectionFpt lfpt rfpt x = (lfpt x, rfpt x)

public export
intersection : Set lfpt -> Set rfpt -> Set (IntersectionFpt lfpt rfpt)
intersection lf rf x = decAnd (lf x) (rf x)

export
elemIntersection : Elem x lfpt -> Elem x rfpt ->
                   Elem x (IntersectionFpt lfpt rfpt)
elemIntersection lprf rprf = (lprf, rprf)

export
notElemIntersectionLeft : NotElem x lfpt ->
                          NotElem x (IntersectionFpt lfpt _)
notElemIntersectionLeft lcontra = lcontra . fst

export
notElemIntersectionRight : NotElem x rfpt ->
                           NotElem x (IntersectionFpt _ rfpt)
notElemIntersectionRight lcontra = lcontra . snd

export
elemIntersectionCommutative : Elem x (IntersectionFpt lfpt rfpt) ->
                              Elem x (IntersectionFpt rfpt lfpt)
elemIntersectionCommutative pprf = (snd pprf, fst pprf)

export
notElemIntersectionCommutative : NotElem x (IntersectionFpt lfpt rfpt) ->
                                 NotElem x (IntersectionFpt rfpt lfpt)
notElemIntersectionCommutative contra (lprf, rprf) = contra (rprf, lprf)

export
elemIntersectionIdempotent : Elem x (IntersectionFpt fpt fpt) ->
                             Elem x fpt
elemIntersectionIdempotent = fst

export
notElemIntersectionIdempotent : NotElem x (IntersectionFpt fpt fpt) ->
                                NotElem x fpt
notElemIntersectionIdempotent contra prf = contra (prf,prf)
