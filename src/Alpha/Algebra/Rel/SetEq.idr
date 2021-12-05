---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.SetEq

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Incl
import Alpha.Algebra.Rel.Prop
import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Set.Set

------------------------
-- Set equality relation
------------------------

public export
data SetEq : Type -> Type -> Type -> Type where
  MkSetEq : (0 lt : Type) -> (0 rt : Type) -> (0 a : Type) -> SetEq lt rt a

public export
setEq : (0 lt : Type) -> (0 rt : Type) -> (0 a : Type) -> SetEq lt rt a
setEq = MkSetEq

public export
0 SetEqPrf : Set lt a => Set rt a => RelPrfTy lt rt
SetEqPrf (ls,rs) = (InclPrf (ls,rs), InclPrf (rs,ls))

public export
Set lt a => Set rt a => Rel (SetEq lt rt a) lt rt where
  RelPrf (MkSetEq lt rt a) = SetEqPrf

--------------------------
-- Set equality properties
--------------------------

public export
Set t a => RelRefl (SetEq t t a) t where
  relRefl (MkSetEq t t a) = (relRefl (MkIncl t t a), relRefl (MkIncl t t a))

public export
Set t a => RelSymm (SetEq t t a) t where
  relSymm (MkSetEq t t a) (lprf,rprf) = (rprf,lprf)

public export
Set t a => RelTrans (SetEq t t a) t where
  relTrans (MkSetEq t t a) (lf,rf) (lg,rg) = (relTrans (MkIncl t t a) lf lg,
                                              relTrans (MkIncl t t a) rg rf)

public export
Set t a => RelAntiSymm (Incl t t a) (SetEq t t a) t where
  relAntiSymm (MkIncl t t a) (MkSetEq t t a) lprf rprf = (lprf,rprf)

--------------------------
-- Set equality projection
--------------------------

public export
0 projectSetEq : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                 SetEqPrf (ls,rs) -> SetPrf ls x -> SetPrf rs x
projectSetEq (lincl,_) prf = projectIncl lincl prf

public export
projectSetEqElem : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                   (0 eprf : SetEqPrf (ls, rs)) -> SetProvenElem ls ->
                   SetProvenElem rs
projectSetEqElem (f,_) pe = projectElem f pe
