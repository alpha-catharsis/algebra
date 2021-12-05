---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Incl

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Prop
import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Set.Set

-------------------------
-- Set inclusion relation
-------------------------

public export
data Incl : Type -> Type -> Type -> Type where
  MkIncl : (0 lt : Type) -> (0 rt : Type) -> (0 a : Type) -> Incl lt rt a

public export
incl : (0 lt : Type) -> (0 rt : Type) -> (0 a : Type) -> Incl lt rt a
incl = MkIncl

public export
0 InclPrf : Set lt a => Set rt a => RelPrfTy lt rt
InclPrf (ls,rs) = {0 e : a} -> SetPrf ls e -> SetPrf rs e

public export
Set lt a => Set rt a => Rel (Incl lt rt a) lt rt where
  RelPrf (MkIncl lt rt a) = InclPrf

---------------------------
-- Set inclusion properties
---------------------------

public export
Set t a => RelRefl (Incl t t a) t where
  relRefl (MkIncl t t a) = id

public export
Set t a => RelTrans (Incl t t a) t where
  relTrans (MkIncl t t a) f g = g . f

---------------------------
-- Set inclusion projection
---------------------------

public export
0 projectIncl : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                InclPrf (ls,rs) -> SetPrf ls x -> SetPrf rs x
projectIncl f lprf = f lprf

public export
projectInclElem : Set lt a => Set rt a => {0 ls : lt} -> {0 rs : rt} ->
                  (0 iprf : InclPrf (ls, rs)) -> SetProvenElem ls ->
                  SetProvenElem rs
projectInclElem f pe = projectElem f pe
