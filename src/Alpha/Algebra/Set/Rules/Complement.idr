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
complRule : {x : a} -> {s : Set a} -> (setPrf s x -> Void) ->
            setPrf (compl s) x
complRule = id

public export
complNotRule : {x : a} -> {s : Set a} -> setPrf s x ->
               setPrf (compl s) x -> Void
complNotRule prf = \f => f prf

public export
invComplRule : {x : a} -> {s : Set a} -> (setPrf (compl s) x -> Void) ->
               setPrf s x
invComplRule prf = void (prf f)
  where f : setPrf s x -> Void
        f prf' = f prf'

public export
invComplNotRule : {x : a} -> {s : Set a} -> setPrf (compl s) x ->
                  setPrf s x -> Void
invComplNotRule = id

--------------------------
-- Double complement rules
--------------------------

public export
dblComplRule : {x : a} -> {s : Set a} -> setPrf s x ->
               setPrf (compl (compl s)) x
dblComplRule prf = \f => f prf

public export
dblComplNotRule : {x : a} -> {s : Set a} -> (setPrf s x -> Void) ->
                  setPrf (compl (compl s)) x -> Void
dblComplNotRule contra = \f => f contra

public export
invDblComplRule : {x : a} -> {s : Set a} -> setPrf (compl (compl s)) x ->
                  setPrf s x
invDblComplRule prf = void (prf f)
  where f : setPrf s x -> Void
        f prf' = f prf'

public export
invDblComplNotRule : {x : a} -> {s : Set a} ->
                     (setPrf (compl (compl s)) x -> Void) -> setPrf s x -> Void
invDblComplNotRule contra = \y => contra (\f => contra
                               (\g => contra (\f1 => contra (\g1 => f y))))
