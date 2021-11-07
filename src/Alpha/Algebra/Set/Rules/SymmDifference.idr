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
symmDiffLeftRule : {x : a} -> {ls : Set a} -> {rs : Set a} -> setPrf ls x ->
                   (setPrf rs x -> Void) -> setPrf (symmDiff ls rs) x
symmDiffLeftRule lprf rcontra = leftUnionRule {ls=diff ls rs} {rs=diff rs ls}
                                (diffRule lprf rcontra)

public export
symmDiffRightRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                    (setPrf ls x -> Void) -> setPrf rs x ->
                    setPrf (symmDiff ls rs) x
symmDiffRightRule lcontra rprf = rightUnionRule {ls=diff ls rs} {rs=diff rs ls}
                                 (diffRule rprf lcontra)

public export
symmDiffNotBothRule : {x : a} -> {ls : Set a} -> {rs : Set a} -> setPrf ls x ->
                      setPrf rs x -> setPrf (symmDiff ls rs) x -> Void
symmDiffNotBothRule lprf rprf = unionNotRule {ls=diff ls rs} {rs=diff rs ls}
                                (diffNotRightRule rprf) (diffNotRightRule lprf)

public export
symmDiffNotNeitherRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                         (setPrf ls x -> Void) -> (setPrf rs x -> Void) ->
                         setPrf (symmDiff ls rs) x -> Void
symmDiffNotNeitherRule lcontra rcontra = unionNotRule {ls=diff ls rs}
                                         {rs=diff rs ls}
                                         (diffNotLeftRule lcontra)
                                         (diffNotLeftRule rcontra)

public export
invSymmDiffLeftRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                      setPrf (symmDiff ls rs) x -> (setPrf rs x -> Void) ->
                      setPrf ls x
invSymmDiffLeftRule eprf rcontra = invDiffLeftRule
                                   (invUnionLeftRule {ls=diff ls rs}
                                   {rs=diff rs ls} eprf
                                   (diffNotLeftRule {ls=rs} rcontra))

public export
invSymmDiffRightRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                       setPrf (symmDiff ls rs) x -> (setPrf ls x -> Void) ->
                       setPrf rs x
invSymmDiffRightRule eprf lcontra = invDiffLeftRule
                                    (invUnionRightRule {ls=diff ls rs}
                                    {rs=diff rs ls} eprf
                                    (diffNotLeftRule lcontra))

public export
invSymmDiffNotLeftRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                         (setPrf (symmDiff ls rs) x -> Void) ->
                         (setPrf rs x -> Void) -> setPrf ls x -> Void
invSymmDiffNotLeftRule econtra rcontra = \y => econtra (Left (y, rcontra))

public export
invSymmDiffNotRightRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                          (setPrf (symmDiff ls rs) x -> Void) ->
                          (setPrf ls x -> Void) -> setPrf rs x -> Void
invSymmDiffNotRightRule econtra lcontra = \y => econtra (Right (y, lcontra))
