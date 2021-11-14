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
diffRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} -> lpty x ->
           (rpty x -> Void) -> DiffPrfTy lpty rpty x
diffRule lpf rcontra = interRule {lpty} {rpty=ComplPrfTy rpty} lpf
                       (complRule {pty=rpty} rcontra)

public export
diffNotLeftRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} ->
                  (lpty x -> Void) -> DiffPrfTy lpty rpty x -> Void
diffNotLeftRule lcontra = interNotLeftRule {lpty} {rpty=ComplPrfTy rpty} lcontra

public export
diffNotRightRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} ->
                   rpty x -> DiffPrfTy lpty rpty x -> Void
diffNotRightRule rpf = interNotRightRule {lpty} {rpty=ComplPrfTy rpty}
                       (complNotRule {pty=rpty} rpf)

public export
invDiffLeftRule : DiffPrfTy lpty rpty x -> lpty x
invDiffLeftRule lpf = invInterLeftRule {lpty} {rpty=ComplPrfTy rpty} lpf

public export
invDiffRightRule : (DiffPrfTy lpty rpty x -> Void) -> lpty x ->
                   rpty x
invDiffRightRule pcontra lpf = invDblComplRule {pty=rpty}
                               (invInterNotRightRule {lpty}
                                {rpty=ComplPrfTy rpty} pcontra lpf)

public export
invDiffNotLeftRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} ->
                     (DiffPrfTy lpty rpty x -> Void) ->
                     (rpty x -> Void) -> lpty x -> Void
invDiffNotLeftRule pcontra rcontra = invInterNotLeftRule {lpty}
                                     {rpty=ComplPrfTy rpty}
                                     pcontra rcontra

public export
invDiffNotRightRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} ->
                      DiffPrfTy lpty rpty x -> rpty x -> Void
invDiffNotRightRule ppf = invComplNotRule {pty=rpty}
                          (invInterRightRule {lpty} {rpty=ComplPrfTy rpty} ppf)
