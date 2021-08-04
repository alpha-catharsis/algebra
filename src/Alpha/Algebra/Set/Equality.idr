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
reflEqualSet s = MkEqualSet (s,s) (reflSubset s) (reflSubset s)

export
symmEqualSet : SymmRel EqualSet
symmEqualSet (MkEqualSet (s,t) fprf bprf) = MkEqualSet (t,s) bprf fprf

export
transEqualSet : TransRel EqualSet
transEqualSet (MkEqualSet (s,t) lfprf lbprf) (MkEqualSet (t,u) rfprf rbprf) =
  MkEqualSet (s,u) (transSubset lfprf rfprf) (transSubset rbprf lbprf)

equivEqualSet : EquivRel EqualSet
equivEqualSet = (reflEqualSet, symmEqualSet, transEqualSet)

export
antiSymmSubset : AntiSymmRel Subset EqualSet
antiSymmSubset lprf@(MkSubset (x,y) _) rprf@(MkSubset (y,x) _) =
  MkEqualSet (x,y) lprf rprf
