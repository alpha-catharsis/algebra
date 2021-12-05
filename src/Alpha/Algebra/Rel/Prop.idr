---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Prop

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Set.Set

---------------------
-- Reflexive relation
---------------------

-- public export
-- 0 RelRefl : RelPrfTy a a -> Type
-- RelRefl prfTy = {x : a} -> prfTy (x,x)

public export
interface Rel t a a => RelRefl t a | t where
  0 relRefl : (r : t) -> {x : a} -> RelPrf r (x,x)

-----------------------
-- Irreflexive relation
-----------------------

-- public export
-- 0 RelIrrefl : RelPrfTy a a -> Type
-- RelIrrefl prfTy = {x : a} -> Not (prfTy (x,x))

public export
interface Rel t a a => RelIrrefl t a | t where
  0 relIrrefl : (r : t) -> {x : a} -> Not (RelPrf r (x,x))

---------------------
-- Symmetric relation
---------------------

-- public export
-- 0 RelSymm : RelPrfTy a a -> Type
-- RelSymm prfTy = {x : a} -> {y : a} -> prfTy (x,y) -> prfTy (y,x)

public export
interface Rel t a a => RelSymm t a | t where
  0 relSymm : (r : t) -> {x : a} -> {y : a} -> RelPrf r (x,y) -> RelPrf r (y,x)

-------------------------
-- Antisymmetric relation
-------------------------

-- public export
-- 0 RelAntiSymm : RelPrfTy a a -> RelPrfTy a a -> Type
-- RelAntiSymm prfTy eqPrfTy = {x : a} -> {y : a} -> prfTy (x,y) -> prfTy (y,x) ->
--                             eqPrfTy (x,y)

-- public export
-- interface Rel t a a => RelAntiSymm t a | t where
--   0 RelEqType : (r : t) -> Type
--   0 relEq : (r : t) -> Rel (RelEqType r) a a => RelEqType r
--   0 relAntiSymm : (r : t) -> Rel (RelEqType r) a a => {x : a} -> {y : a} ->
--                   RelPrf r (x,y) -> RelPrf r (y,x) -> RelPrf (relEq r) (x,y)

public export
interface Rel t a a => Rel teq a a => RelAntiSymm t teq a | t where
  0 relAntiSymm : (r : t) -> (req : teq) -> {x : a} -> {y : a} ->
                  RelPrf r (x,y) -> RelPrf r (y,x) -> RelPrf req (x,y)


---------------------
-- Asymmetric relation
---------------------

-- public export
-- 0 RelAsymm : RelPrfTy a a -> Type
-- RelAsymm prfTy = {x : a} -> {y : a} -> prfTy (x,y) -> Not (prfTy (y,x))

public export
interface Rel t a a => RelAsymm t a | t where
  0 relAsymm : (r : t) -> {x : a} -> {y : a} -> RelPrf r (x,y) ->
               Not (RelPrf r (y,x))

----------------------
-- Transitive relation
----------------------

-- public export
-- 0 RelTrans : RelPrfTy a a -> Type
-- RelTrans prfTy = {x : a} -> {y : a} -> {z : a} -> prfTy (x,y) -> prfTy (y,z) ->
--                  prfTy (x,z)

public export
interface Rel t a a => RelTrans t a | t where
  0 relTrans : (r : t) -> {x : a} -> {y : a} -> {z : a} -> RelPrf r (x,y) ->
               RelPrf r (y,z) -> RelPrf r (x,z)
