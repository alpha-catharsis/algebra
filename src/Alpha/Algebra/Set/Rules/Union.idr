---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Union

-------------------
-- Internal imports
-------------------

import public Alpha.Algebra.Set.Ops
import public Alpha.Algebra.Set.Set

--------------
-- Union rules
--------------

public export
leftUnionRule : {x : a} -> {s : Set a} -> {s' : Set a} -> fst s x ->
                fst (union s s') x
leftUnionRule prf = Left prf

public export
rightUnionRule : {x : a} -> {s : Set a} -> {s' : Set a} -> fst s' x ->
                 fst (union s s') x
rightUnionRule prf' = Right prf'

public export
invUnionRule : {x : a} -> {s : Set a} -> {s' : Set a} -> fst (union s s') x ->
               Either (fst s x) (fst s' x)
invUnionRule = id
