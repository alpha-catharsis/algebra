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
0 RelPty : (SetPty a, SetPty b) -> Type
RelPty (lspty, rspty) = (ProvenElem lspty, ProvenElem rspty) -> Type

public export
0 Rel : RelPty (lspty, rspty) -> Type
Rel rpty = (ppe : (ProvenElem lspty, ProvenElem rspty)) -> Dec (rpty ppe)

public export
areRelated : (lpe : ProvenElem lspty) -> (rpe : ProvenElem rspty) ->
             {0 rpty : RelPty (lspty,rspty)} -> Rel rpty -> Dec (rpty (lpe,rpe))
areRelated lpe rpe r = r (lpe,rpe)

public export
related : (lpe : ProvenElem lspty) -> (rpe : ProvenElem rspty) ->
          {0 rpty : RelPty (lspty, rspty)} -> Rel rpty -> Bool
related lpe rpe r = isYes (areRelated lpe rpe r)

-----------------
-- Proven related
-----------------

public export
0 ProvenRelated : RelPty (lspty,rspty) -> Type
ProvenRelated rpty = Subset (ProvenElem lspty, ProvenElem rspty) rpty

public export
0 DisprovenRelated : RelPty (lspty, rspty) -> Type
DisprovenRelated rpty = ProvenRelated (Not . rpty)

public export
0 EitherRelated : RelPty (lspty, rspty) -> Type
EitherRelated rpty = Either (DisprovenRelated rpty) (ProvenRelated rpty)

public export
provenRelated : {0 rpty : RelPty (lspty,rspty)} -> ProvenRelated rpty ->
                (ProvenElem lspty, ProvenElem rspty)
provenRelated = fst

public export
0 provenRelatedPrf : (pr : ProvenRelated rpty) -> rpty (provenRelated pr)
provenRelatedPrf = snd

public export
projectRelated : {0 rpty : RelPty (lspty,rspty)} ->
                 {0 rpty' : RelPty (lspty,rspty)} ->
                 (0 f : {ppe : (ProvenElem lspty, ProvenElem rspty)} ->
                        rpty ppe -> rpty' ppe) ->
                 ProvenRelated rpty -> ProvenRelated rpty'
projectRelated f pr = Element (provenRelated pr) (f (provenRelatedPrf pr))

