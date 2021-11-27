---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Compl

-------------------
-- External imports
-------------------

import Data.DPair

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Rel.Incl
import Alpha.Algebra.Rel.SetEq
import Alpha.Algebra.Set.Basic
import Alpha.Algebra.Set.Ops
import Alpha.Algebra.Set.Set

-------------------
-- Complement rules
-------------------

public export
0 complRule : {pty : SetPty a} -> Not (pty x) -> ComplPty pty x
complRule = id

public export
complElem : DisprovenElem pty -> ProvenElem (ComplPty pty)
complElem = projectElem (complRule {pty})

public export
0 complNotRule : {pty : SetPty a} -> pty x -> Not (ComplPty pty x)
complNotRule prf = \f => f prf

public export
complNotElem : ProvenElem pty -> DisprovenElem (ComplPty pty)
complNotElem = projectElem (complNotRule {pty})

public export
0 invComplRule : Not (ComplPty pty x) -> pty x
invComplRule prf = void (prf ?f)
    where f : Not (pty x)
          f prf' = f prf'

invComplElem : DisprovenElem (ComplPty pty) -> ProvenElem pty
invComplElem = projectElem (invComplRule {pty})

public export
0 invComplNotRule : ComplPty pty x -> Not (pty x)
invComplNotRule = id

invComplNotElem : ProvenElem (ComplPty pty) -> DisprovenElem pty
invComplNotElem = projectElem (invComplNotRule {pty})

--------------------------
-- Double complement rules
--------------------------

public export
0 dblComplRule : {pty : SetPty a} -> pty x -> ComplPty (ComplPty pty) x
dblComplRule prf = \f => f prf

public export
dblComplElem : ProvenElem pty -> ProvenElem (ComplPty (ComplPty pty))
dblComplElem = projectElem (dblComplRule {pty})

public export
0 dblComplNotRule : {pty : SetPty a} -> Not (pty x) ->
                    Not (ComplPty (ComplPty pty) x)
dblComplNotRule contra = \f => f contra

public export
dblComplNotElem : DisprovenElem pty -> DisprovenElem (ComplPty (ComplPty pty))
dblComplNotElem = projectElem (dblComplNotRule {pty})

public export
0 invDblComplRule : ComplPty (ComplPty pty) x -> pty x
invDblComplRule prf = void (prf f)
  where f : Not (pty x)
        f prf' = f prf'

public export
invDblComplElem : ProvenElem (ComplPty (ComplPty pty)) -> ProvenElem pty
invDblComplElem = projectElem (invDblComplRule {pty})

public export
0 invDblComplNotRule : Not (ComplPty (ComplPty pty) x) -> Not (pty x)
invDblComplNotRule contra = \y => contra (\f => contra
                               (\g => contra (\f1 => contra (\g1 => f y))))

public export
invDblComplNotElem : DisprovenElem (ComplPty (ComplPty pty)) ->
                     DisprovenElem pty
invDblComplNotElem = projectElem (invDblComplNotRule {pty})

------------------------
-- Complement equalities
------------------------

public export
0 setEqUnivComplEmpty : SetEqPty (UnivPty, ComplPty EmptyPty)
setEqUnivComplEmpty = (\x,f => f x, \_ => ())

public export
projectUnivComplEmpty : {a : Type} -> ProvenElem (UnivPty {a}) ->
                        ProvenElem (ComplPty (EmptyPty {a}))
projectUnivComplEmpty = projectSetEqElem setEqUnivComplEmpty
