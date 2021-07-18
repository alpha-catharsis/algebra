---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Inclusion

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Equality
import Alpha.Algebra.Set.Set

---------------------
-- Subset data type
---------------------

public export
data Subset : Set a -> Set a -> Type where
  MkSubset : (ls : Set a) -> (rs : Set a) ->
               (prf : {x : a} -> Elem x ls -> Elem x rs) -> Subset ls rs

export
inclusionReflexive : (s : Set a) -> Subset s s
inclusionReflexive s = MkSubset s s id

export
inclusionTransitive : (ls : Set a) -> (ms : Set a) -> (rs : Set a) ->
                      Subset ls ms -> Subset ms rs -> Subset ls rs
inclusionTransitive ls ms rs (MkSubset ls ms lprf) (MkSubset ms rs rprf) =
  MkSubset ls rs (rprf . lprf)

export
inclusionAntiSymmetric : (ls : Set a) -> (rs : Set a) ->
                         Subset ls rs -> Subset rs ls -> EqualSet ls rs
inclusionAntiSymmetric ls rs (MkSubset ls rs prf) (MkSubset rs ls rprf) =
  MkEqualSet ls rs prf rprf
