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
0 Rel : Type -> Type -> Type
Rel a b = (a,b) -> Type

public export
0 DecRel : Rel a b -> Type
DecRel r = (p : (a,b)) -> Dec (r p)

public export
areRelated : DecRel r -> (x : a) -> (y : b) -> Dec (r (x,y))
areRelated dr x y = dr (x,y)

public export
related : {0 r : Rel a b} -> DecRel r -> (x : a) -> (y : b) -> Bool
related dr x y = isYes (areRelated dr x y)

-------------------------------
-- Proven and disproven related
-------------------------------

public export
data ProvenRelated : Rel a b -> Type where
  MkProvenRelated : (p : (a,b)) -> (0 prf : r p) -> ProvenRelated r

public export
provenRelated : {0 r : Rel a b} -> ProvenRelated r -> (a,b)
provenRelated (MkProvenRelated p _) = p

public export
0 relatedPrf : (pr : ProvenRelated r) -> r (provenRelated pr)
relatedPrf (MkProvenRelated _ prf) = prf

public export
DisprovenRelated : Rel a b -> Type
DisprovenRelated r = ProvenRelated (Not . r)

public export
projectRelated : {0 r : Rel a b} -> {0 r' : Rel a b} -> (0 f : {p : (a,b)} -> r p -> r' p) ->
                 ProvenRelated r -> ProvenRelated r'
projectRelated f pr = MkProvenRelated (provenRelated pr) (f (relatedPrf pr))

public export
EitherRelated : Rel a b -> Type
EitherRelated r = Either (DisprovenRelated r) (ProvenRelated r)

public export
eitherRelated : {0 r : Rel a b} -> DecRel r -> (x : a) -> (y : b) -> EitherRelated r
eitherRelated dr x y = case areRelated dr x y of
  No contra => Left (MkProvenRelated (x,y) contra)
  Yes prf => Right (MkProvenRelated (x,y) prf)
