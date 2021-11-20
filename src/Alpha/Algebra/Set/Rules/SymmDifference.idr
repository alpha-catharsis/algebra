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
0 symmDiffLeftRule : SetPrf ls x -> (SetPrf rs x -> Void) ->
                     SetPrf (symmDiff ls rs) x
symmDiffLeftRule lprf rcontra = leftUnionRule {ls=diff ls rs} {rs=diff rs ls}
                                (diffRule lprf rcontra)


public export
0 symmDiffRightRule : (SetPrf ls x -> Void) -> SetPrf rs x ->
                      SetPrf (symmDiff ls rs) x
symmDiffRightRule lcontra rprf = rightUnionRule {ls=diff ls rs} {rs=diff rs ls}
                                 (diffRule rprf lcontra)

public export
0 symmDiffNotBothRule : SetPrf ls x -> SetPrf rs x ->
                        SetPrf (symmDiff ls rs) x -> Void
symmDiffNotBothRule lprf rprf = unionNotRule {ls=diff ls rs} {rs=diff rs ls}
                                (diffNotRightRule rprf)
                                (diffNotRightRule lprf)

public export
0 symmDiffNotNeitherRule : (SetPrf ls x -> Void) -> (SetPrf rs x -> Void) ->
                           SetPrf (symmDiff ls rs) x -> Void
symmDiffNotNeitherRule lcontra rcontra = unionNotRule {ls=diff ls rs}
                                         {rs=diff rs ls}
                                         (diffNotLeftRule lcontra)
                                         (diffNotLeftRule rcontra)

public export
0 invSymmDiffLeftRule : SetPrf (symmDiff ls rs) x -> (SetPrf rs x -> Void) ->
                        SetPrf ls x
invSymmDiffLeftRule eprf rcontra = invDiffLeftRule
                                   (invUnionLeftRule {ls=diff ls rs}
                                    {rs=diff rs ls} eprf
                                    (diffNotLeftRule rcontra))

public export
0 invSymmDiffRightRule : SetPrf (symmDiff ls rs) x -> (SetPrf ls x -> Void) ->
                         SetPrf rs x
invSymmDiffRightRule eprf lcontra = invDiffLeftRule
                                    (invUnionRightRule {ls=diff ls rs}
                                     {rs=diff rs ls} eprf
                                     (diffNotLeftRule lcontra))

public export
0 invSymmDiffNotLeftRule : (SetPrf (symmDiff ls rs) x -> Void) ->
                           (SetPrf rs x -> Void) -> SetPrf ls x -> Void
invSymmDiffNotLeftRule econtra rcontra = \y => econtra (Left (y, rcontra))

public export
0 invSymmDiffNotRightRule : (SetPrf (symmDiff ls rs) x -> Void) ->
                            (SetPrf ls x -> Void) -> SetPrf rs x -> Void
invSymmDiffNotRightRule econtra lcontra = \y => econtra (Right (y, lcontra))
