---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Intersection

-------------------
-- Internal imports
-------------------

import public Alpha.Algebra.Set.Ops
import public Alpha.Algebra.Set.Set

---------------------
-- Intersection rules
---------------------

public export
interRule : {x : a} -> {s : Set a} -> {s' : Set a} -> fst s x ->
            fst s' x -> fst (inter s s') x
interRule prf prf' = (prf, prf')

public export
invLeftInterRule : {x : a} -> {s : Set a} -> {s' : Set a} ->
                   fst (inter s s') x -> fst s x
invLeftInterRule (prf, _) = prf

public export
invRightInterRule : {x : a} -> {s : Set a} -> {s' : Set a} ->
                    fst (inter s s') x -> fst s' x
invRightInterRule (_, prf') = prf'
