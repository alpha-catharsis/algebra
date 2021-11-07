---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Union

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Ops
import Alpha.Algebra.Set.Set

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
unionNotRule : {x : a} -> {s : Set a} -> {s' : Set a} -> (fst s x -> Void) ->
               (fst s' x -> Void) -> fst (union s s') x -> Void
unionNotRule contra contra' eprf = case eprf of
  Left prf => contra prf
  Right prf' => contra' prf'

public export
invUnionRule : {x : a} -> {s : Set a} -> {s' : Set a} -> fst (union s s') x ->
               Either (fst s x) (fst s' x)
invUnionRule = id

public export
invUnionNotRule : {x : a} -> {s : Set a} -> {s' : Set a} ->
                  (fst (union s s') x -> Void) -> (fst s x, fst s' x) -> Void
invUnionNotRule contra pprf = contra (Left (fst pprf))
