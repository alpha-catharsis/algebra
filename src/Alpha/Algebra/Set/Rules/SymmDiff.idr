---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.SymmDiff

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Rules.Diff
import Alpha.Algebra.Set.Rules.Union
import Alpha.Algebra.Set.Ops
import Alpha.Algebra.Set.Set

-----------------------------
-- Symmetric difference rules
-----------------------------

public export
0 symmDiffLeftRule : {lpty : SetPty a} -> {rpty : SetPty a} -> lpty x ->
                     Not (rpty x) -> SymmDiffPty lpty rpty x
symmDiffLeftRule lprf rcontra = leftUnionRule {lpty=DiffPty lpty rpty}
                                {rpty=DiffPty rpty lpty}
                                (diffRule {lpty} {rpty} lprf rcontra)


public export
0 symmDiffRightRule : {lpty : SetPty a} -> {rpty : SetPty a} -> Not (lpty x) ->
                      rpty x -> SymmDiffPty lpty rpty x
symmDiffRightRule lcontra rprf = rightUnionRule {lpty=DiffPty lpty rpty}
                                 {rpty=DiffPty rpty lpty}
                                 (diffRule {lpty=rpty} {rpty=lpty} rprf lcontra)

public export
0 symmDiffNotBothRule : {lpty : SetPty a} -> {rpty : SetPty a} -> lpty x ->
                        rpty x -> Not (SymmDiffPty lpty rpty x)
symmDiffNotBothRule lprf rprf = unionNotRule {lpty=DiffPty lpty rpty}
                                {rpty=DiffPty rpty lpty}
                                (diffNotRightRule {lpty} {rpty} rprf)
                                (diffNotRightRule {lpty=rpty} {rpty=lpty} lprf)

public export
0 symmDiffNotNeitherRule : {lpty : SetPty a} -> {rpty : SetPty a} ->
                           Not (lpty x) -> Not (rpty x) ->
                           Not (SymmDiffPty lpty rpty x)
symmDiffNotNeitherRule lcontra rcontra = unionNotRule {lpty=DiffPty lpty rpty}
                                         {rpty=DiffPty rpty lpty}
                                         (diffNotLeftRule {lpty} {rpty} lcontra)
                                         (diffNotLeftRule {lpty=rpty}
                                          {rpty=lpty} rcontra)

public export
0 invSymmDiffLeftRule : SymmDiffPty lpty rpty x -> Not (rpty x) -> lpty x
invSymmDiffLeftRule eprf rcontra = invDiffLeftRule {lpty} {rpty}
                                   (invUnionLeftRule {lpty=DiffPty lpty rpty}
                                    {rpty=DiffPty rpty lpty} eprf
                                    (diffNotLeftRule {lpty=rpty} {rpty=lpty}
                                     rcontra))

public export
0 invSymmDiffRightRule : SymmDiffPty lpty rpty x -> Not (lpty x) -> rpty x
invSymmDiffRightRule eprf lcontra = invDiffLeftRule {lpty=rpty} {rpty=lpty}
                                    (invUnionRightRule {lpty=DiffPty lpty rpty}
                                     {rpty=DiffPty rpty lpty} eprf
                                     (diffNotLeftRule {lpty} {rpty}
                                      lcontra))

public export
0 invSymmDiffNotLeftRule : Not (SymmDiffPty lpty rpty x) ->
                           Not (rpty x) -> Not (lpty x)
invSymmDiffNotLeftRule econtra rcontra = \y => econtra (Left (y, rcontra))

public export
0 invSymmDiffNotRightRule : Not (SymmDiffPty lpty rpty x) ->
                            Not (lpty x) -> Not (rpty x)
invSymmDiffNotRightRule econtra lcontra = \y => econtra (Right (y, lcontra))
