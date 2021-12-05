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
0 symmDiffLeftRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                     SetPrf ls x -> Not (SetPrf rs x) -> SymmDiffPrf ls rs x
symmDiffLeftRule lprf rcontra = unionLeftRule {ls=diff ls rs} {rs=diff rs ls}
                                (diffRule lprf rcontra)

public export
0 symmDiffRightRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                      Not (SetPrf ls x) -> SetPrf rs x -> SymmDiffPrf ls rs x
symmDiffRightRule lcontra rprf = unionRightRule {ls=diff ls rs} {rs=diff rs ls}
                                 (diffRule rprf lcontra)

public export
0 symmDiffNotBothRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                        SetPrf ls x -> SetPrf rs x -> Not (SymmDiffPrf ls rs x)
symmDiffNotBothRule lprf rprf = unionNotRule {ls=diff ls rs} {rs=diff rs ls}
                                (diffNotRightRule rprf)
                                (diffNotRightRule lprf)

public export
0 symmDiffNotNeitherRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                           Not (SetPrf ls x) -> Not (SetPrf rs x) ->
                           Not (SymmDiffPrf ls rs x)
symmDiffNotNeitherRule lcontra rcontra = unionNotRule {ls=diff ls rs}
                                         {rs = diff rs ls}
                                         (diffNotLeftRule lcontra)
                                         (diffNotLeftRule rcontra)

public export
0 invSymmDiffLeftRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                        SymmDiffPrf ls rs x -> Not (SetPrf rs x) -> SetPrf ls x
invSymmDiffLeftRule eprf rcontra = invDiffLeftRule
                                   (invUnionLeftRule {ls=diff ls rs}
                                    {rs=diff rs ls} eprf
                                    (diffNotLeftRule rcontra))

public export
0 invSymmDiffRightRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                         SymmDiffPrf ls rs x -> Not (SetPrf ls x) -> SetPrf rs x
invSymmDiffRightRule eprf lcontra = invDiffLeftRule
                                    (invUnionRightRule {ls=diff ls rs}
                                     {rs=diff rs ls} eprf
                                     (diffNotLeftRule lcontra))

public export
0 invSymmDiffNotLeftRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                           Not (SymmDiffPrf ls rs x) ->
                           Not (SetPrf rs x) -> Not (SetPrf ls x)
invSymmDiffNotLeftRule econtra rcontra = \y => econtra (Left (y, rcontra))

public export
0 invSymmDiffNotRightRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                            Not (SymmDiffPrf ls rs x) -> Not (SetPrf ls x) ->
                            Not (SetPrf rs x)
invSymmDiffNotRightRule econtra lcontra = \y => econtra (Right (y, lcontra))
