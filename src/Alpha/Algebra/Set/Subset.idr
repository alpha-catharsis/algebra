---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Subset

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
import Alpha.Algebra.Relation

-------------------
-- Subset data type
-------------------

public export
data Subset : RelFpt (Set a) (Set a) where
  MkSubset : (ss : (Set a, Set a)) ->
             (prf : {x : a} -> Elem x (fst ss) -> Elem x (snd ss)) ->
             Subset ss

export
notSubset : (ss : (Set a, Set a)) -> (x : a) ->
            Elem x (fst ss) -> (Elem x (snd ss) -> Void) ->
            Subset ss -> Void
notSubset _ _ lprf rcontra (MkSubset _ f) = rcontra (f lprf)

--------------------
-- Subset properties
--------------------

export
reflSubset : ReflRel Subset
reflSubset = \s => MkSubset (s,s) id

export
transSubset : TransRel Subset
transSubset = \(MkSubset (s,t) lf),
               (MkSubset (t,u) rf) =>
              MkSubset (s,u) (rf . lf)
