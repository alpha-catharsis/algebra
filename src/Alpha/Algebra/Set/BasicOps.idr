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
ComplementPrf : SetFpt a -> SetFpt a
ComplementPrf fpt = Not . fpt

public export
complement : SetFn fpt -> SetFn (ComplementPrf fpt)
complement f x = decNot (f x)

export
elemComplement : SetContra fpt x -> SetPrf (ComplementPrf fpt) x
elemComplement = id

export
notElemComplement : SetPrf fpt x -> SetContra (ComplementPrf fpt) x
notElemComplement prf cprf = cprf prf

elemComplement2 : {fpt : SetFpt a} -> SetPrf fpt x ->
                  SetPrf (ComplementPrf (ComplementPrf fpt)) x
elemComplement2 prf f = f prf

export
notElemComplement2 : (SetContra fpt x) ->
                     SetContra (ComplementPrf (ComplementPrf fpt)) x
notElemComplement2 contra f = f contra

------------
-- Set union
------------

public export
UnionPrf : SetFpt a -> SetFpt a -> SetFpt a
UnionPrf lfpt rfpt a = Either (lfpt a) (rfpt a)

public export
union : SetFn lfpt -> SetFn rfpt -> SetFn (UnionPrf lfpt rfpt)
union lf rf x = decOr (lf x) (rf x)

export
elemUnionLeft : SetPrf lfpt x -> SetPrf (UnionPrf lfpt _) x
elemUnionLeft prf = Left prf

export
elemUnionRight : SetPrf rfpt x -> SetPrf (UnionPrf _ rfpt) x
elemUnionRight prf = Right prf

export
notElemUnion : SetContra lfpt x -> SetContra rfpt x ->
               SetContra (UnionPrf lfpt rfpt) x
notElemUnion lcontra rcontra = either lcontra rcontra

export
elemUnionCommutative : SetPrf (UnionPrf lfpt rfpt) x ->
                       SetPrf (UnionPrf rfpt lfpt) x
elemUnionCommutative eprf = case eprf of
  Left lprf => Right lprf
  Right rprf => Left rprf

export
notElemUnionCommutative : SetContra (UnionPrf lfpt rfpt) x ->
                          SetContra (UnionPrf rfpt lfpt) x
notElemUnionCommutative contra pprf = case pprf of
  Left lprf => contra (Right lprf)
  Right rprf => contra (Left rprf)

export
elemUnionIdempotent : SetPrf (UnionPrf fpt fpt) x -> SetPrf fpt x
elemUnionIdempotent eprf = case eprf of
  Left lprf => lprf
  Right rprf => rprf

export
notElemUnionIdempotent : SetContra (UnionPrf fpt fpt) x -> SetContra fpt x
notElemUnionIdempotent contra prf = contra (Left prf)

-------------------
-- Set intersection
-------------------

public export
IntersectionPrf : SetFpt a -> SetFpt a -> SetFpt a
IntersectionPrf lfpt rfpt a = (lfpt a, rfpt a)

public export
intersection : SetFn lfpt -> SetFn rfpt -> SetFn (IntersectionPrf lfpt rfpt)
intersection lf rf x = decAnd (lf x) (rf x)

export
elemIntersection : SetPrf lfpt x -> SetPrf rfpt x ->
                   SetPrf (IntersectionPrf lfpt rfpt) x
elemIntersection lprf rprf = (lprf, rprf)

export
notElemIntersectionLeft : SetContra lfpt x ->
                          SetContra (IntersectionPrf lfpt _) x
notElemIntersectionLeft lcontra = lcontra . fst

export
notElemIntersectionRight : SetContra rfpt x ->
                          SetContra (IntersectionPrf _ rfpt) x
notElemIntersectionRight lcontra = lcontra . snd

export
elemIntersectionCommutative : SetPrf (IntersectionPrf lfpt rfpt) x ->
                              SetPrf (IntersectionPrf rfpt lfpt) x
elemIntersectionCommutative pprf = (snd pprf, fst pprf)

export
notElemIntersectionCommutative : SetContra (IntersectionPrf lfpt rfpt) x ->
                                 SetContra (IntersectionPrf rfpt lfpt) x
notElemIntersectionCommutative contra (lprf, rprf) = contra (rprf, lprf)

export
elemIntersectionIdempotent : SetPrf (IntersectionPrf fpt fpt) x ->
                             SetPrf fpt x
elemIntersectionIdempotent = fst

export
notElemIntersectionIdempotent : SetContra (IntersectionPrf fpt fpt) x ->
                                SetContra fpt x
notElemIntersectionIdempotent contra prf = contra (prf,prf)
