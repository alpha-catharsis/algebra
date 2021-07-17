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
data Subset : Set lfpt a -> Set rfpt a -> Type where
  MkSubset : (ls : Set lfpt a) -> (rs : Set rfpt a) ->
               (prf : {x : a} -> Elem x ls -> Elem x rs) -> Subset ls rs

export
inclusionReflexive : (s : Set fpt a) -> Subset s s
inclusionReflexive s = MkSubset s s id

export
inclusionTransitive : (ls : Set lftp a) -> (ms : Set mfpt a) ->
                      (rs : Set rfpt a) -> Subset ls ms -> Subset ms rs ->
                      Subset ls rs
inclusionTransitive ls ms rs (MkSubset ls ms lprf) (MkSubset ms rs rprf) =
  MkSubset ls rs (rprf . lprf)

export
inclusionAntiSymmetric : (ls : Set lfpt a) -> (rs : Set rfpt a) ->
                         Subset ls rs -> Subset rs ls -> Equality.Equal ls rs
inclusionAntiSymmetric ls rs (MkSubset ls rs prf) (MkSubset rs ls rprf) =
  MkEqual ls rs prf rprf
