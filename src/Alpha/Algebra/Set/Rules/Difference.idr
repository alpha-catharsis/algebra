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
0 diffRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} -> lpty x ->
             (rpty x -> Void) -> DiffPrfTy lpty rpty x
diffRule lpf rcontra = interRule {lpty} {rpty=ComplPrfTy rpty} lpf
                       (complRule {pty=rpty} rcontra)

public export
0 diffNotLeftRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} ->
                    (lpty x -> Void) -> DiffPrfTy lpty rpty x -> Void
diffNotLeftRule lcontra = interNotLeftRule {lpty} {rpty=ComplPrfTy rpty} lcontra

public export
0 diffNotRightRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} ->
                     rpty x -> DiffPrfTy lpty rpty x -> Void
diffNotRightRule rpf = interNotRightRule {lpty} {rpty=ComplPrfTy rpty}
                       (complNotRule {pty=rpty} rpf)

public export
0 invDiffLeftRule : DiffPrfTy lpty rpty x -> lpty x
invDiffLeftRule lpf = invInterLeftRule {lpty} {rpty=ComplPrfTy rpty} lpf

public export
0 invDiffRightRule : (DiffPrfTy lpty rpty x -> Void) -> lpty x ->
                     rpty x
invDiffRightRule pcontra lpf = invDblComplRule {pty=rpty}
                               (invInterNotRightRule {lpty}
                                {rpty=ComplPrfTy rpty} pcontra lpf)

public export
0 invDiffNotLeftRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} ->
                       (DiffPrfTy lpty rpty x -> Void) ->
                       (rpty x -> Void) -> lpty x -> Void
invDiffNotLeftRule pcontra rcontra = invInterNotLeftRule {lpty}
                                     {rpty=ComplPrfTy rpty}
                                     pcontra rcontra

public export
0 invDiffNotRightRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} ->
                        DiffPrfTy lpty rpty x -> rpty x -> Void
invDiffNotRightRule ppf = invComplNotRule {pty=rpty}
                          (invInterRightRule {lpty} {rpty=ComplPrfTy rpty} ppf)
