---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Difference

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Rules.Complement
import Alpha.Algebra.Set.Rules.Intersection
import Alpha.Algebra.Set.Ops
import Alpha.Algebra.Set.Set

-------------------
-- Difference rules
-------------------

public export
diffRule : {x : a} -> {s : Set a} -> {s' : Set a} -> fst s x ->
           (fst s' x -> Void) -> fst (diff s s') x
diffRule prf contra = interRule {s'=compl s'} prf (complRule contra)

public export
diffNotLeftRule : {x : a} -> {s : Set a} -> {s' : Set a} ->
                  (fst s x -> Void) -> fst (diff s s') x -> Void
diffNotLeftRule contra = interNotLeftRule {s'=compl s'} contra

public export
diffNotRightRule : {x : a} -> {s : Set a} -> {s' : Set a} ->
                   fst s' x -> fst (diff s s') x -> Void
diffNotRightRule contra' = interNotRightRule {s'=compl s'}
                             (complNotRule contra')

public export
invDiffLeftRule : {x : a} -> {s : Set a} -> {s' : Set a} ->
                  fst (diff s s') x -> fst s x
invDiffLeftRule prf = invLeftInterRule {s'=compl s'} prf

public export
invDiffRightRule : {x : a} -> {s : Set a} -> {s' : Set a} ->
                   (fst (diff s s') x -> Void) -> fst s x ->
                   fst s' x
invDiffRightRule dcontra prf = invDblComplRule (invInterNotRightRule
                                                {s'=compl s'} dcontra prf)

public export
invDiffNotLeftRule : {x : a} -> {s : Set a} -> {s' : Set a} ->
                     (fst (diff s s') x -> Void) -> (fst s' x -> Void) ->
                     fst s x -> Void
invDiffNotLeftRule dcontra contra' = invInterNotLeftRule {s'=compl s'}
                                     dcontra contra'

public export
invDiffNotRightRule : {x : a} -> {s : Set a} -> {s' : Set a} ->
                      fst (diff s s') x -> fst s' x -> Void
invDiffNotRightRule dprf = invComplNotRule
                           (invRightInterRule dprf {s'=compl s'})
