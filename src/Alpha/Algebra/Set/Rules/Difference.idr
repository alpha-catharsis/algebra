---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Difference

-------------------
-- Internal imports
-------------------

import public Alpha.Algebra.Set.Rules.Complement
import public Alpha.Algebra.Set.Rules.Intersection
import public Alpha.Algebra.Set.Ops
import public Alpha.Algebra.Set.Set

-------------------
-- Difference rules
-------------------

public export
diffRule : {x : a} -> {s : Set a} -> {s' : Set a} -> fst s x ->
           (fst s' x -> Void) -> fst (diff s s') x
diffRule prf contra = interRule {s'=compl s'} prf (complRule contra)

public export
invDiffRule : {x : a} -> {s : Set a} -> {s' : Set a} -> fst (diff s s') x ->
              fst s x
invDiffRule prf = invLeftInterRule {s'=compl s'} prf
