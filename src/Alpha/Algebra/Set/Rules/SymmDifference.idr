---------------------
-- Module declaration
---------------------

  module Alpha.Algebra.Set.Rules.SymmDifference

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Rules.Difference
import Alpha.Algebra.Set.Rules.Union
import Alpha.Algebra.Set.Ops
import Alpha.Algebra.Set.Set

-----------------------------
-- Symmetric difference rules
-----------------------------

-- public export
-- symmDiffLeftRule : {x : a} -> {s : Set a} -> {s' : Set a} -> fst s x ->
--                    (fst s' x -> Void) -> fst (symmDiff s s') x
-- symmDiffLeftRule prf contra = unionRule {s = diff s s'} {s' = diff s' s}
--                               (diffRule prf conra) (complRule contra)
