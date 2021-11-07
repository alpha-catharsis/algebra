---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Complement

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Ops
import Alpha.Algebra.Set.Set

-------------------
-- Complement rules
-------------------

public export
complRule : {x : a} -> {s : Set a} -> (fst s x -> Void) -> fst (compl s) x
complRule = id

public export
complNotRule : {x : a} -> {s : Set a} -> fst s x -> fst (compl s) x -> Void
complNotRule prf = \f => f prf

public export
invComplRule : {x : a} -> {s : Set a} -> (fst (compl s) x -> Void) -> fst s x
invComplRule prf = void (prf f)
  where f : fst s x -> Void
        f prf' = f prf'

public export
invComplNotRule : {x : a} -> {s : Set a} -> fst (compl s) x -> fst s x -> Void
invComplNotRule = id

--------------------------
-- Double complement rules
--------------------------

public export
dblComplRule : {x : a} -> {s : Set a} -> fst s x -> fst (compl (compl s)) x
dblComplRule prf = \f => f prf

public export
dblComplNotRule : {x : a} -> {s : Set a} -> (fst s x -> Void) ->
                  fst (compl (compl s)) x -> Void
dblComplNotRule contra = \f => f contra

public export
invDblComplRule : {x : a} -> {s : Set a} -> fst (compl (compl s)) x -> fst s x
invDblComplRule prf = void (prf f)
  where f : fst s x -> Void
        f prf' = f prf'

public export
invDblComplNotRule : {x : a} -> {s : Set a} ->
                     (fst (compl (compl s)) x -> Void) -> fst s x -> Void
invDblComplNotRule contra = \y => contra (\f => contra
                               (\g => contra (\f1 => contra (\g1 => f y))))
