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

-- import Alpha.Algebra.Rel.Rel
-- import Alpha.Algebra.Rel.Incl
-- import Alpha.Algebra.Rel.SetEq
-- import Alpha.Algebra.Set.Basic
import Alpha.Algebra.Set.Ops
import Alpha.Algebra.Set.Set

--------------
-- Basic rules
--------------

public export
0 complRule : (s : Set a) -> Not (s x) -> Compl s x
complRule _ = id

public export
0 complNotRule : (s : Set a) -> s x -> Not (Compl s x)
complNotRule _ prf = \f => f prf

public export
0 dblComplRule : (s : Set a) -> s x -> Compl (Compl s) x
dblComplRule s = complNotRule s

public export
0 invComplRule : (s : Set a) -> Not (Compl s x) -> s x
invComplRule s prf = void (prf f)
  where f : Not (s x)
        f prf' = assert_total (f prf')

public export
0 invComplNotRule : (s : Set a) -> Compl s x -> Not (s x)
invComplNotRule _ = id

public export
0 invDblComplRule : (s : Set a) -> Compl (Compl s) x -> s x
invDblComplRule s = invComplRule s

----------------------
-- Basic element rules
----------------------

public export
complElem : DisprovenElem s -> ProvenElem (Compl s)
complElem = projectElem (complRule s)

public export
complNotElem : ProvenElem s -> DisprovenElem (Compl s)
complNotElem = projectElem (complNotRule s)

public export
dblComplElem : ProvenElem s -> ProvenElem (Compl (Compl s))
dblComplElem = projectElem (dblComplRule s)

public export
invComplElem : DisprovenElem (Compl s) -> ProvenElem s
invComplElem = projectElem (invComplRule s)

public export
invComplNotElem : ProvenElem (Compl s) -> DisprovenElem s
invComplNotElem = projectElem (invComplNotRule s)

public export
invDblComplElem : ProvenElem (Compl (Compl s)) -> ProvenElem s
invDblComplElem = projectElem (invDblComplRule s)

------------------------
-- Complement equalities
------------------------

-- public export
-- 0 setEqUnivComplEmpty : {a : Type} -> SetEqPrf (MkUniv, compl MkEmpty)
-- setEqUnivComplEmpty = (\_ => id, \_ => ())

-- public export
-- projectUnivComplEmpty : {0 a : Type} -> ProvenElem {a} UnivPrf ->
--                         ProvenElem {a} (ComplPrf MkEmpty)
-- projectUnivComplEmpty = projectSetEqElem {ls=MkUniv} {rs=compl MkEmpty}
--                         setEqUnivComplEmpty
