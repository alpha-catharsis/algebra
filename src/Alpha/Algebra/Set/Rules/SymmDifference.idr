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
symmDiffLeftRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} -> lpty x ->
                   (rpty x -> Void) -> SymmDiffPrfTy lpty rpty x
symmDiffLeftRule lpf rcontra = leftUnionRule {lpty=DiffPrfTy lpty rpty}
                                {rpty=DiffPrfTy rpty lpty}
                                (diffRule {lpty} {rpty} lpf rcontra)

public export
symmDiffRightRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} ->
                    (lpty x -> Void) -> rpty x ->
                    SymmDiffPrfTy lpty rpty x
symmDiffRightRule lcontra rpf = rightUnionRule {lpty=DiffPrfTy lpty rpty}
                                 {rpty=DiffPrfTy rpty lpty}
                                 (diffRule {lpty=rpty} {rpty=lpty} rpf lcontra)

public export
symmDiffNotBothRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} -> lpty x ->
                      rpty x -> SymmDiffPrfTy lpty rpty x -> Void
symmDiffNotBothRule lpf rpf = unionNotRule {lpty=DiffPrfTy lpty rpty}
                                {rpty=DiffPrfTy rpty lpty}
                                (diffNotRightRule {lpty} {rpty} rpf)
                                (diffNotRightRule {lpty=rpty} {rpty=lpty} lpf)

public export
symmDiffNotNeitherRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} ->
                         (lpty x -> Void) -> (rpty x -> Void) ->
                         SymmDiffPrfTy lpty rpty x -> Void
symmDiffNotNeitherRule lcontra rcontra = unionNotRule {lpty=DiffPrfTy lpty rpty}
                                         {rpty=DiffPrfTy rpty lpty}
                                         (diffNotLeftRule {lpty} {rpty} lcontra)
                                         (diffNotLeftRule {lpty=rpty}
                                          {rpty=lpty} rcontra)

public export
invSymmDiffLeftRule : {rpty : SetPrfTy a} -> {lpty : SetPrfTy a} ->
                      SymmDiffPrfTy lpty rpty x -> (rpty x -> Void) -> lpty x
invSymmDiffLeftRule epf rcontra = invDiffLeftRule {lpty} {rpty}
                                  (invUnionLeftRule {lpty=DiffPrfTy lpty rpty}
                                   {rpty=DiffPrfTy rpty lpty} epf
                                   (diffNotLeftRule {lpty=rpty} {rpty=lpty}
                                    rcontra))

public export
invSymmDiffRightRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} ->
                       SymmDiffPrfTy lpty rpty x -> (lpty x -> Void) ->
                       rpty x
invSymmDiffRightRule epf lcontra = invDiffLeftRule {lpty=rpty} {rpty=lpty}
                                    (invUnionRightRule
                                     {lpty=DiffPrfTy lpty rpty}
                                     {rpty=DiffPrfTy rpty lpty} epf
                                     (diffNotLeftRule {lpty} {rpty} lcontra))

public export
invSymmDiffNotLeftRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} ->
                         (SymmDiffPrfTy lpty rpty x -> Void) ->
                         (rpty x -> Void) -> lpty x -> Void
invSymmDiffNotLeftRule econtra rcontra = \y => econtra (Left (y, rcontra))

public export
invSymmDiffNotRightRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} ->
                          (SymmDiffPrfTy lpty rpty x -> Void) ->
                          (lpty x -> Void) -> rpty x -> Void
invSymmDiffNotRightRule econtra lcontra = \y => econtra (Right (y, lcontra))
