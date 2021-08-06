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
Complement : Set a -> Set a
Complement s = Not . s

public export
complement : SetDec s -> SetDec (Complement s)
complement f x = decNot (f x)

export
elemComplement : NotElem x s -> Elem x (Complement s)
elemComplement = id

export
notElemComplement : Elem x s -> NotElem x (Complement s)
notElemComplement prf cprf = cprf prf

elemComplement2 : {s : Set a} -> Elem x s ->
                  Elem x (Complement (Complement s))
elemComplement2 prf f = f prf

export
notElemComplement2 : (NotElem x s) ->
                     NotElem x (Complement (Complement s))
notElemComplement2 contra f = f contra

------------
-- Set union
------------

public export
Union : Set a -> Set a -> Set a
Union ls rs x = Either (ls x) (rs x)

public export
union : SetDec ls -> SetDec rs -> SetDec (Union ls rs)
union lf rf x = decOr (lf x) (rf x)

export
elemUnionLeft : Elem x ls -> Elem x (Union ls _)
elemUnionLeft prf = Left prf

export
elemUnionRight : Elem x rs -> Elem x (Union _ rs)
elemUnionRight prf = Right prf

export
notElemUnion : NotElem x ls -> NotElem x rs ->
               NotElem x (Union ls rs)
notElemUnion lcontra rcontra = either lcontra rcontra

export
elemUnionCommutative : Elem x (Union ls rs) ->
                       Elem x (Union rs ls)
elemUnionCommutative eprf = case eprf of
  Left lprf => Right lprf
  Right rprf => Left rprf

export
notElemUnionCommutative : NotElem x (Union ls rs) ->
                          NotElem x (Union rs ls)
notElemUnionCommutative contra pprf = case pprf of
  Left lprf => contra (Right lprf)
  Right rprf => contra (Left rprf)

export
elemUnionIdempotent : Elem x (Union fpt fpt) -> Elem x fpt
elemUnionIdempotent eprf = case eprf of
  Left lprf => lprf
  Right rprf => rprf

export
notElemUnionIdempotent : NotElem x (Union fpt fpt) -> NotElem x fpt
notElemUnionIdempotent contra prf = contra (Left prf)

-------------------
-- Set intersection
-------------------

public export
Intersection : Set a -> Set a -> Set a
Intersection ls rs x = (ls x, rs x)

public export
intersection : SetDec ls -> SetDec rs -> SetDec (Intersection ls rs)
intersection lf rf x = decAnd (lf x) (rf x)

export
elemIntersection : Elem x ls -> Elem x rs ->
                   Elem x (Intersection ls rs)
elemIntersection lprf rprf = (lprf, rprf)

export
notElemIntersectionLeft : NotElem x ls ->
                          NotElem x (Intersection ls _)
notElemIntersectionLeft lcontra = lcontra . fst

export
notElemIntersectionRight : NotElem x rs ->
                           NotElem x (Intersection _ rs)
notElemIntersectionRight lcontra = lcontra . snd

export
elemIntersectionCommutative : Elem x (Intersection ls rs) ->
                              Elem x (Intersection rs ls)
elemIntersectionCommutative pprf = (snd pprf, fst pprf)

export
notElemIntersectionCommutative : NotElem x (Intersection ls rs) ->
                                 NotElem x (Intersection rs ls)
notElemIntersectionCommutative contra (lprf, rprf) = contra (rprf, lprf)

export
elemIntersectionIdempotent : Elem x (Intersection fpt fpt) ->
                             Elem x fpt
elemIntersectionIdempotent = fst

export
notElemIntersectionIdempotent : NotElem x (Intersection fpt fpt) ->
                                NotElem x fpt
notElemIntersectionIdempotent contra prf = contra (prf,prf)
