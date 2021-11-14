---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Union

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Ops
import Alpha.Algebra.Set.Set

--------------
-- Union rules
--------------

public export
leftUnionRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} -> lpty x ->
                UnionPrfTy lpty rpty x
leftUnionRule lpf = Left lpf

public export
rightUnionRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} -> rpty x ->
                 UnionPrfTy lpty rpty x
rightUnionRule rpf = Right rpf

public export
unionNotRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} ->
               (lpty x -> Void) -> (rpty x -> Void) ->
               UnionPrfTy lpty rpty x -> Void
unionNotRule lcontra rcontra eprf = case eprf of
  Left lpf => lcontra lpf
  Right rpf => rcontra rpf

public export
invUnionRule : UnionPrfTy lpty rpty x -> Either (lpty x) (rpty x)
invUnionRule = id

public export
invUnionLeftRule : UnionPrfTy lpty rpty x -> (rpty x -> Void) ->
                   lpty x
invUnionLeftRule eprf rcontra = case eprf of
  Left lpf => lpf
  Right rpf => void (rcontra rpf)

public export
invUnionRightRule : UnionPrfTy lpty rpty x -> (lpty x -> Void) ->
                    rpty x
invUnionRightRule epf lcontra = case epf of
  Left lpf => void (lcontra lpf)
  Right rpf => rpf

public export
invUnionNotRule : (UnionPrfTy lpty rpty x -> Void) ->
                  (lpty x, rpty x) -> Void
invUnionNotRule econtra pf = econtra (Left (fst pf))
