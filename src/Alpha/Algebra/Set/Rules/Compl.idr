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
0 dblComplRule : Set t a => {s : t} -> SetPrf s x -> ComplPrf (compl s) x
dblComplRule prf = \f => f prf

public export
dblComplElem : Set t a => {0 s : t} -> ProvenElem (SetPrf s) ->
               ProvenElem (ComplPrf (compl s))
dblComplElem = projectElem dblComplRule

public export
0 invDblComplRule : Set t a => {s : t} -> ComplPrf (compl s) x -> SetPrf s x
invDblComplRule prf = assert_total (void (prf f))
  where f : Not (SetPrf s x)
        f prf' = assert_total (f prf')

invDblComplElem : Set t a => {0 s : t} -> ProvenElem (ComplPrf (compl s)) ->
                  ProvenElem (SetPrf s)
invDblComplElem = projectElem invDblComplRule

------------------------
-- Complement equalities
------------------------

public export
0 setEqUnivComplEmpty : {a : Type} -> SetEqPrf (MkUniv, compl MkEmpty)
setEqUnivComplEmpty = (\_ => id, \_ => ())

public export
projectUnivComplEmpty : {0 a : Type} -> ProvenElem {a} UnivPrf ->
                        ProvenElem {a} (ComplPrf MkEmpty)
projectUnivComplEmpty = projectSetEqElem {ls=MkUniv} {rs=compl MkEmpty}
                        setEqUnivComplEmpty
