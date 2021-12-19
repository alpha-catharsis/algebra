---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Diff

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Rules.Compl
import Alpha.Algebra.Set.Rules.Inter
import Alpha.Algebra.Set.Ops
import Alpha.Algebra.Set.Set

--------------
-- Basic rules
--------------

public export
0 diffRule : (ls : Set a) -> (rs : Set a) -> ls x -> Not (rs x) -> Diff ls rs x
diffRule ls rs lprf rcontra = interRule ls (Compl rs) lprf rcontra

public export
0 diffNotLeftRule : (ls : Set a) -> (rs : Set a) -> Not (ls x) -> Not (Diff ls rs x)
diffNotLeftRule ls rs lcontra = interNotLeftRule ls (Compl rs) lcontra

public export
0 diffNotRightRule : (ls : Set a) -> (rs : Set a) -> rs x -> Not (Diff ls rs x)
diffNotRightRule ls rs rprf = interNotRightRule ls (Compl rs) (dblComplRule rs rprf)

public export
0 invDiffLeftRule : (ls : Set a) -> (rs : Set a) -> Diff ls rs x -> ls x
invDiffLeftRule ls rs pprf = invInterLeftRule ls (Compl rs) pprf

public export
0 invDiffRightRule : (ls : Set a) -> (rs : Set a) -> Not (Diff ls rs x) -> ls x -> rs x
invDiffRightRule ls rs pcontra lprf = invDblComplRule rs (invInterNotRightRule ls (Compl rs) pcontra lprf)

public export
0 invDiffNotLeftRule : (ls : Set a) -> (rs : Set a) -> Not (Diff ls rs x) -> Not (rs x) -> Not (ls x)
invDiffNotLeftRule ls rs pcontra rcontra = invInterNotLeftRule ls (Compl rs) pcontra rcontra

public export
0 invDiffNotRightRule : (ls : Set a) -> (rs : Set a) -> Diff ls rs x -> Not (rs x)
invDiffNotRightRule ls rs pprf = invInterRightRule ls (Compl rs) pprf

----------------------
-- Basic element rules
----------------------

public export
diffNotLeftElem : DisprovenElem ls -> DisprovenElem (Diff ls rs)
diffNotLeftElem = projectElem (diffNotLeftRule ls rs)

public export
diffNotRightElem : ProvenElem rs -> DisprovenElem (Diff ls rs)
diffNotRightElem = projectElem (diffNotRightRule ls rs)

public export
invDiffLeftElem : ProvenElem (Diff ls rs) -> ProvenElem ls
invDiffLeftElem = projectElem (invDiffLeftRule ls rs)

public export
invDiffNotRightElem : ProvenElem (Diff ls rs) -> DisprovenElem rs
invDiffNotRightElem = projectElem (invDiffNotRightRule ls rs)
