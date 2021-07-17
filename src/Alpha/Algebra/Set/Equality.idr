---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

--------------------
-- Included data type
---------------------

public export
data Equal : Set lfpt a -> Set rfpt a -> Type where
  MkEqual : (ls : Set lfpt a) -> (rs : Set rfpt a) ->
            (prf : {x : a} -> Elem x ls -> Elem x rs) ->
            (rprf : {x : a} -> Elem x rs -> Elem x ls) -> Equal ls rs

export
equalityReflexive : (s : Set fpt a) -> Equality.Equal s s
equalityReflexive s = MkEqual s s id id

export
equalityTransitive : (ls : Set lftp a) -> (ms : Set mfpt a) ->
                     (rs : Set rfpt a) -> Equality.Equal ls ms ->
                     Equality.Equal ms rs -> Equality.Equal ls rs
equalityTransitive ls ms rs (MkEqual ls ms lprf lrprf)
                   (MkEqual ms rs rprf rrprf) =
  MkEqual ls rs (rprf . lprf) (lrprf . rrprf)

export
equalitySymmetric : (ls : Set lftp a) -> (rs : Set rfpt a) ->
                    Equality.Equal ls rs -> Equality.Equal rs ls
equalitySymmetric ls rs (MkEqual ls rs prf rprf) = MkEqual rs ls rprf prf
