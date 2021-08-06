---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.BasicOps

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Relation.Relation
import Alpha.Algebra.Relation.Set
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
notElemUnion : NotElem x ls -> NotElem x rs ->
               NotElem x (Union ls rs)
notElemUnion lcontra rcontra = either lcontra rcontra

export
subsetUnionLeft : {s : Set a} -> Related (s, (Union s _)) Subset
subsetUnionLeft = Left

export
subsetUnionRight : {s : Set a} -> Related (s, (Union _ s)) Subset
subsetUnionRight = Right

export
subsetUnionCommutative : {ls : Set a} -> {rs : Set a} ->
                         Related (Union ls rs, Union rs ls) Subset
subsetUnionCommutative ef = case ef of
  Left f => Right f
  Right f => Left f

export
equalUnionCommutative : {ls : Set a} -> {rs : Set a} ->
                        Related (Union ls rs, Union rs ls) EqualSet
equalUnionCommutative = (subsetUnionCommutative {ls} {rs},
                         subsetUnionCommutative {ls=rs} {rs=ls})

export
subsetUnionIdempotent : {ls : Set a} ->
                        Related (ls, Union ls ls) Subset
subsetUnionIdempotent = Left

export
equalUnionIdempotent : {ls : Set a} ->
                       Related (ls, Union ls ls) EqualSet
equalUnionIdempotent = (Left, \ef => case ef of
                                       Left f => f
                                       Right f => f)

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

--

export
subsetIntersectionLeft : {ls : Set a} ->
                         Related (Intersection ls _, ls) Subset
subsetIntersectionLeft = fst

export
subsetIntersectionRight : {rs : Set a} ->
                          Related (Intersection _ rs, rs) Subset
subsetIntersectionRight = snd

export
subsetIntersectionCommutative : {ls : Set a} -> {rs : Set a} ->
                                Related (Intersection ls rs,
                                         Intersection rs ls) Subset
subsetIntersectionCommutative (f,g) = (g,f)

export
subsetIntersectionIdempotent : {ls : Set a} ->
                               Related (ls, Intersection ls ls) Subset
subsetIntersectionIdempotent f = (f, f)

export
equalIntersectionIdempotent : {ls : Set a} ->
                              Related (ls, Intersection ls ls) EqualSet
equalIntersectionIdempotent = (\f => (f, f), fst)
