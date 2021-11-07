---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Complement

-------------------
-- Internal imports
-------------------

import public Alpha.Algebra.Set.Ops
import public Alpha.Algebra.Set.Set

--------------------------
-- Complement rules
--------------------------

public export
complRule : {x : a} -> {s : Set a} -> (fst s x -> Void) -> fst (compl s) x
complRule = id

public export
invComplRule : {x : a} -> {s : Set a} -> (fst (compl s) x -> Void) -> fst s x
invComplRule prf = void (prf f)
  where f : fst s x -> Void
        f prf' = f prf'

--------------------------
-- Double complement rules
--------------------------

public export
dblComplRule : {x : a} -> {s : Set a} -> fst s x -> fst (compl (compl s)) x
dblComplRule prf = \f => f prf

public export
invDblComplRule : {x : a} -> {s : Set a} -> fst (compl (compl s)) x -> fst s x
invDblComplRule prf = void (prf f)
  where f : fst s x -> Void
        f prf' = f prf'
