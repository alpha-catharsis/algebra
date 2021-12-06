---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Rel

-------------------
-- External imports
-------------------

import Data.DPair
import Decidable.Decidable

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

----------------------
-- Relation definition
----------------------

public export
0 RelPrfTy : Type -> Type -> Type
RelPrfTy a b = (a,b) -> Type

public export
interface Rel t a b | t where
  0 RelPrf : t -> RelPrfTy a b

public export
interface Rel t a b => DecRel t a b | t where
  areRelated : (r : t) -> (x : a) -> (y : b) -> Dec (RelPrf r (x,y))

public export
related : DecRel t a b => (r : t) -> (x : a) -> (y : b) -> Bool
related r x y = isYes (areRelated r x y)

-------------------------------
-- Proven and disproven related
-------------------------------

public export
record ProvenRelated {0 a : Type} {0 b : Type } (0 prfTy : RelPrfTy a b) where
  constructor MkProvenRelated
  provenRelated : (a,b)
  0 relatedPrf : prfTy provenRelated

public export
0 DisprovenRelated : RelPrfTy a b -> Type
DisprovenRelated prfTy = ProvenRelated (Not . prfTy)

public export
projectRelated : {0 prfTy : RelPrfTy a b} -> {0 prfTy' : RelPrfTy a b} ->
                 (0 f : {x : a} -> {y : b} -> prfTy (x,y) -> prfTy' (x,y)) ->
                 ProvenRelated prfTy -> ProvenRelated prfTy'
projectRelated f (MkProvenRelated (x,y) prf) = MkProvenRelated (x,y) (f prf)

public export
0 EitherRelated : RelPrfTy a b -> Type
EitherRelated prfTy = Either (DisprovenRelated prfTy) (ProvenRelated prfTy)

public export
eitherRelated : DecRel t a b => (r : t) -> (x : a) -> (y : b) ->
                 EitherRelated (RelPrf r)
eitherRelated r x y = case areRelated r x y of
  No contra => Left (MkProvenRelated (x,y) contra)
  Yes prf => Right (MkProvenRelated (x,y) prf)

----------------------------------------
-- Relation proven and disproven related
----------------------------------------

public export
0 RelProvenRelated : Rel t a b => t -> Type
RelProvenRelated r = ProvenRelated (RelPrf r)

public export
0 RelDisprovenRelated : Rel t a b => t -> Type
RelDisprovenRelated r = DisprovenRelated (RelPrf r)
