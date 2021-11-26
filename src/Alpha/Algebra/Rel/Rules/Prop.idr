---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Rules.Prop

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Set.Set

---------------------
-- Reflexive relation
---------------------

public export
0 RelRefl : RelPty (spty,spty) -> Type
RelRefl rpty = {pe : ProvenElem spty} -> rpty (pe,pe)

-----------------------
-- Irreflexive relation
-----------------------

public export
0 RelIrrefl : RelPty (spty,spty) -> Type
RelIrrefl rpty = {pe : ProvenElem spty} -> Not (rpty (pe,pe))

---------------------
-- Symmetric relation
---------------------

public export
0 RelSymm : RelPty (spty,spty) -> Type
RelSymm rpty = {lpe : ProvenElem spty} -> {rpe : ProvenElem spty} ->
               rpty (lpe,rpe) -> rpty (rpe,lpe)

-------------------------
-- Antisymmetric relation
-------------------------

public export
0 RelAntiSymm : RelPty (spty,spty) -> RelPty (spty,spty) -> Type
RelAntiSymm rpty eqpty = {lpe : ProvenElem spty} -> {rpe : ProvenElem spty} ->
                         rpty (lpe,rpe) -> rpty (rpe,lpe) -> eqpty (lpe,rpe)

---------------------
-- Asymmetric relation
---------------------

public export
0 RelAsymm : RelPty (spty,spty) -> Type
RelAsymm rpty = {lpe : ProvenElem spty} -> {rpe : ProvenElem spty} ->
                rpty (lpe,rpe) -> Not (rpty (rpe,lpe))


----------------------
-- Transitive relation
----------------------

public export
0 RelTrans : RelPty (spty,spty) -> Type
RelTrans rpty = {lpe : ProvenElem spty} -> {mpe : ProvenElem spty} ->
                {rpe : ProvenElem spty} -> rpty (lpe,mpe) -> rpty (mpe,rpe) ->
                rpty (lpe,rpe)
