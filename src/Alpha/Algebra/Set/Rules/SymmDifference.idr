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

public export
symmDiffLeftRule : {x : a} -> {s : Set a} -> {s' : Set a} -> fst s x ->
                   (fst s' x -> Void) -> fst (symmDiff s s') x
symmDiffLeftRule prf contra = leftUnionRule {s = diff s s'} {s' = diff s' s}
                              (diffRule prf contra)

public export
symmDiffRightRule : {x : a} -> {s : Set a} -> {s' : Set a} ->
                    (fst s x -> Void) -> fst s' x -> fst (symmDiff s s') x
symmDiffRightRule contra prf = rightUnionRule {s = diff s s'} {s' = diff s' s}
                               (diffRule prf contra)

public export
symmDiffNotBothRule : {x : a} -> {s : Set a} -> {s' : Set a} -> fst s x ->
                       fst s' x -> fst (symmDiff s s') x -> Void
symmDiffNotBothRule prf prf' = unionNotRule {s = diff s s'} {s' = diff s' s}
                               (diffNotRightRule prf') (diffNotRightRule prf)

public export
symmDiffNotNeitherRule : {x : a} -> {s : Set a} -> {s' : Set a} ->
                         (fst s x -> Void) -> (fst s' x -> Void) ->
                         fst (symmDiff s s') x -> Void
symmDiffNotNeitherRule contra contra' = unionNotRule {s = diff s s'}
                                       {s' = diff s' s}
                                       (diffNotLeftRule contra)
                                       (diffNotLeftRule contra')

public export
invSymmDiffLeftRule : {x : a} -> {s : Set a} -> {s' : Set a} ->
                      fst (symmDiff s s') x -> (fst s' x -> Void) ->
                      fst s x
invSymmDiffLeftRule dprf contra' = invDiffLeftRule
                                   (invUnionLeftRule {s=diff s s'}
                                   {s'=diff s' s} dprf (diffNotLeftRule {s=s'}
                                                        contra'))

public export
invSymmDiffRightRule : {x : a} -> {s : Set a} -> {s' : Set a} ->
                       fst (symmDiff s s') x -> (fst s x -> Void) ->
                       fst s' x
invSymmDiffRightRule = ?d

public export
invSymmDiffNotLeftRule : {x : a} -> {s : Set a} -> {s' : Set a} ->
                         (fst (symmDiff s s') x -> Void) ->
                         (fst s' x -> Void) -> fst s x -> Void
invSymmDiffNotLeftRule = ?e

public export
invSymmDiffNotRightRule : {x : a} -> {s : Set a} -> {s' : Set a} ->
                          (fst (symmDiff s s') x -> Void) ->
                          (fst s x -> Void) -> fst s' x -> Void
invSymmDiffNotRightRule = ?f
