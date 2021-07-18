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
data EqualSet : Set a -> Set a -> Type where
  MkEqualSet : (ls : Set a) -> (rs : Set a) ->
            (prf : {x : a} -> Elem x ls -> Elem x rs) ->
            (rprf : {x : a} -> Elem x rs -> Elem x ls) -> EqualSet ls rs

export
equalityReflexive : (s : Set a) -> EqualSet s s
equalityReflexive s = MkEqualSet s s id id

export
equalityTransitive : (ls : Set a) -> (ms : Set a) -> (rs : Set a) ->
                     EqualSet ls ms -> EqualSet ms rs -> EqualSet ls rs
equalityTransitive ls ms rs (MkEqualSet ls ms lprf lrprf)
                   (MkEqualSet ms rs rprf rrprf) =
  MkEqualSet ls rs (rprf . lprf) (lrprf . rrprf)

export
equalitySymmetric : (ls : Set a) -> (rs : Set a) ->
                    EqualSet ls rs -> EqualSet rs ls
equalitySymmetric ls rs (MkEqualSet ls rs prf rprf) = MkEqualSet rs ls rprf prf
