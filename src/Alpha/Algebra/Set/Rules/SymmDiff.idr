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

--------------
-- Basic rules
--------------

public export
0 symmDiffLeftRule : (ls : Set a) -> (rs : Set a) -> ls x -> Not (rs x) -> SymmDiff ls rs x
symmDiffLeftRule ls rs lprf rcontra = unionLeftRule (Diff ls rs) (Diff rs ls) (diffRule ls rs lprf rcontra)

public export
0 symmDiffRightRule : (ls : Set a) -> (rs : Set a) -> Not (ls x) -> rs x -> SymmDiff ls rs x
symmDiffRightRule ls rs lcontra rprf = unionRightRule (Diff ls rs) (Diff rs ls) (diffRule rs ls rprf lcontra)

public export
0 symmDiffNotBothRule : (ls : Set a) -> (rs : Set a) -> ls x -> rs x -> Not (SymmDiff ls rs x)
symmDiffNotBothRule ls rs lprf rprf = unionNotRule (Diff ls rs) (Diff rs ls) (diffNotRightRule ls rs rprf)
                                      (diffNotRightRule rs ls lprf)

public export
0 symmDiffNotNeitherRule : (ls : Set a) -> (rs : Set a) -> Not (ls x) -> Not (rs x) -> Not (SymmDiff ls rs x)
symmDiffNotNeitherRule ls rs lcontra rcontra = unionNotRule (Diff ls rs) (Diff rs ls) (diffNotLeftRule ls rs lcontra)
                                               (diffNotLeftRule rs ls rcontra)

public export
0 invSymmDiffLeftRule : (ls : Set a) -> (rs : Set a) -> SymmDiff ls rs x -> Not (rs x) -> ls x
invSymmDiffLeftRule ls rs eprf rcontra = invDiffLeftRule ls rs (invUnionLeftRule (Diff ls rs) (Diff rs ls) eprf
                                                                (diffNotLeftRule rs ls rcontra))

public export
0 invSymmDiffRightRule : (ls : Set a) -> (rs : Set a) -> SymmDiff ls rs x -> Not (ls x) -> rs x
invSymmDiffRightRule ls rs eprf lcontra = invDiffLeftRule rs ls (invUnionRightRule (Diff ls rs) (Diff rs ls) eprf
                                                                 (diffNotLeftRule ls rs lcontra))

public export
0 invSymmDiffNotLeftRule : (ls : Set a) -> (rs : Set a) -> Not (SymmDiff ls rs x) -> Not (rs x) -> Not (ls x)
invSymmDiffNotLeftRule _ _ econtra rcontra = \y => econtra (Left (y, rcontra))

public export
0 invSymmDiffNotRightRule : (ls : Set a) -> (rs : Set a) -> Not (SymmDiff ls rs x) -> Not (ls x) -> Not (rs x)
invSymmDiffNotRightRule _ _ econtra lcontra = \y => econtra (Right (y, lcontra))
