---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Relation
import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.Subset

---------------------
-- EqualSet data type
---------------------

public export
data EqualSet : RelFpt (Set a) (Set a) where
  MkEqualSet : (ss : (Set a, Set a)) ->
               Subset ss -> Subset (snd ss, fst ss) ->
               EqualSet ss

notEqualSetLeft : (ss : (Set a, Set a)) ->
                (Subset ss -> Void) -> EqualSet ss -> Void
notEqualSetLeft _ lcontra (MkEqualSet _ lprf _) = lcontra lprf

notEqualSetRight : (ss : (Set a, Set a)) ->
                   (Subset (snd ss, fst ss) -> Void) -> EqualSet ss -> Void
notEqualSetRight _ rcontra (MkEqualSet _ _ rprf) = rcontra rprf

----------------------
-- EqualSet properties
----------------------

export
reflEqualSet : ReflRel EqualSet
reflEqualSet = \s => MkEqualSet (s,s) (reflSubset s) (reflSubset s)

export
symmEqualSet : SymmRel EqualSet
symmEqualSet = \(MkEqualSet (s,t) fprf bprf) => MkEqualSet (t,s) bprf fprf

export
transEqualSet : TransRel EqualSet
transEqualSet = \(MkEqualSet (s,t) lfprf lbprf),
                 (MkEqualSet (t,u) rfprf rbprf) =>
                MkEqualSet (s,u) (transSubset lfprf rfprf)
                           (transSubset rbprf lbprf)

export
antiSymmSubset : AntiSymmRel Subset EqualSet
antiSymmSubset = \lprf@(MkSubset (x,y) _), rprf@(MkSubset (y,x) _) =>
                 MkEqualSet (x,y) lprf rprf

-- public export
-- data EqualSet : Set a -> Set a -> Type where
--   MkEqualSet : (ls : Set a) -> (rs : Set a) ->
--             (prf : {x : a} -> Elem x ls -> Elem x rs) ->
--             (rprf : {x : a} -> Elem x rs -> Elem x ls) -> EqualSet ls rs

-- export
-- equalityReflexive : (s : Set a) -> EqualSet s s
-- equalityReflexive s = MkEqualSet s s id id

-- export
-- equalityTransitive : (ls : Set a) -> (ms : Set a) -> (rs : Set a) ->
--                      EqualSet ls ms -> EqualSet ms rs -> EqualSet ls rs
-- equalityTransitive ls ms rs (MkEqualSet ls ms lprf lrprf)
--                    (MkEqualSet ms rs rprf rrprf) =
--   MkEqualSet ls rs (rprf . lprf) (lrprf . rrprf)

-- export
-- equalitySymmetric : (ls : Set a) -> (rs : Set a) ->
--                     EqualSet ls rs -> EqualSet rs ls
-- equalitySymmetric ls rs (MkEqualSet ls rs prf rprf) = MkEqualSet rs ls rprf prf
