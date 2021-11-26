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

-------------------
-- Difference rules
-------------------

public export
0 diffRule : {lpty : SetPty a} -> {rpty : SetPty a} -> lpty x ->
             Not (rpty x) -> DiffPty lpty rpty x
diffRule lprf rcontra = interRule {lpty} {rpty=ComplPty rpty} lprf
                        (complRule {pty=rpty} rcontra)


public export
0 diffNotLeftRule : {lpty : SetPty a} -> Not (lpty x) ->
                    Not (DiffPty lpty rpty x)
diffNotLeftRule lcontra = interNotLeftRule {lpty} {rpty=ComplPty rpty} lcontra

public export
diffNotLeftElem : DisprovenElem lpty -> DisprovenElem (DiffPty lpty rpty)
diffNotLeftElem = projectElem (diffNotLeftRule {lpty} {rpty})

public export
0 diffNotRightRule : {rpty : SetPty a} -> rpty x ->
                     Not (DiffPty lpty rpty x)
diffNotRightRule rprf = interNotRightRule {lpty} {rpty=ComplPty rpty}
                        (complNotRule {pty=rpty} rprf)

public export
diffNotRightElem : ProvenElem rpty -> DisprovenElem (DiffPty lpty rpty)
diffNotRightElem = projectElem (diffNotRightRule {lpty} {rpty})

public export
0 invDiffLeftRule : DiffPty lpty rpty x -> lpty x
invDiffLeftRule lprf = invInterLeftRule {lpty} {rpty=ComplPty rpty} lprf

public export
invDiffLeftElem : ProvenElem (DiffPty lpty rpty) -> ProvenElem lpty
invDiffLeftElem = projectElem (invDiffLeftRule {lpty} {rpty})

public export
0 invDiffRightRule : Not (DiffPty lpty rpty x) -> lpty x -> rpty x
invDiffRightRule pcontra lprf = invDblComplRule {pty=rpty}
                                (invInterNotRightRule {lpty}
                                 {rpty=ComplPty rpty} pcontra lprf)

public export
0 invDiffNotLeftRule : Not (DiffPty lpty rpty x) -> Not (rpty x) ->
                       Not (lpty x)
invDiffNotLeftRule pcontra rcontra = invInterNotLeftRule {lpty}
                                     {rpty=ComplPty rpty} pcontra rcontra

public export
0 invDiffNotRightRule : DiffPty lpty rpty x -> Not (rpty x)
invDiffNotRightRule pprf = invComplNotRule {pty=rpty}
                           (invInterRightRule {lpty} {rpty=ComplPty rpty} pprf)

public export
invDiffNotRightElem : ProvenElem (DiffPty lpty rpty) -> DisprovenElem rpty
invDiffNotRightElem = projectElem (invDiffNotRightRule {lpty} {rpty})
