---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.SetEq

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Rel.Incl
import Alpha.Algebra.Set.Set

------------------------
-- Set equality relation
------------------------

-- public export
-- data SetEq : Type where
--   MkSetEq : SetEq

-- public export
-- setEq : SetEq
-- setEq = MkSetEq

-- public export
-- 0 SetEqPrf : Set lt a => Set rt a => RelPrfTy lt rt
-- SetEqPrf (ls,rs) = (InclPrf (ls,rs), InclPrf (rs,ls))

-- public export
-- Set lt a => Set rt a => Rel SetEq lt rt where
--   RelPrf _ = SetEqPrf

--------------------------
-- Set equality projection
--------------------------

-- public export
-- 0 projectSetEq : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
--                  SetEqPrf (ls,rs) -> SetPrf ls x -> SetPrf rs x
-- projectSetEq (f,_) prf = f prf

-- public export
-- projectSetEqElem : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
--                    (0 eprf : SetEqPrf (ls, rs)) -> SetProvenElem ls ->
--                    SetProvenElem rs
-- projectSetEqElem (f,_) lpe = projectElem f lpe
