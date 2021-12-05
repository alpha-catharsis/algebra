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
data Incl : Type -> Type where
  MkIncl : (0 a : Type) -> Incl a

public export
incl : (0 a : Type) -> Incl a
incl a = MkIncl a

public export
0 InclPrf : Set lt a => Set rt a => RelPrfTy lt rt
InclPrf (ls,rs) = (e : a) -> SetPrf ls e -> SetPrf rs e

public export
Set lt a => Set rt a => Rel (Incl a) lt rt where
  RelPrf _ = InclPrf

---------------------------
-- Set inclusion properties
---------------------------

public export
Set t a => RelRefl (Incl a) t where
  relRefl _ _ lprf = lprf

public export
Set t a => RelTrans (Incl a) t where
  relTrans _ f g e lprf = g e (f e lprf)

---------------------------
-- Set inclusion projection
---------------------------

-- public export
-- 0 projectIncl : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
--                 InclPrf (ls,rs) -> SetPrf ls x -> SetPrf rs x
-- projectIncl f lprf = f lprf

-- public export
-- projectInclElem : Set lt a => Set rt a => {0 ls : lt} -> {0 rs : rt} ->
--                   (0 iprf : InclPrf (ls, rs)) -> SetProvenElem ls ->
--                   SetProvenElem rs
-- projectInclElem f lpe = projectElem f lpe
