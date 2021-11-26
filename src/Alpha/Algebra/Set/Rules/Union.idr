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
0 leftUnionRule : {lpty : SetPty a} -> lpty x -> UnionPty lpty rpty x
leftUnionRule = Left

public export
leftUnionElem : ProvenElem lpty -> ProvenElem (UnionPty lpty rpty)
leftUnionElem = projectElem (leftUnionRule {lpty} {rpty})

public export
0 rightUnionRule : {rpty : SetPty a} -> rpty x -> UnionPty lpty rpty x
rightUnionRule = Right

public export
rightUnionElem : ProvenElem rpty -> ProvenElem (UnionPty lpty rpty)
rightUnionElem = projectElem (rightUnionRule {lpty} {rpty})

public export
0 unionNotRule : {lpty : SetPty a} -> {rpty : SetPty a} ->
                 Not (lpty x) -> Not (rpty x) -> Not (UnionPty lpty rpty x)
unionNotRule lcontra rcontra eprf = case eprf of
  Left lprf => lcontra lprf
  Right rprf => rcontra rprf

public export
0 invUnionRule : UnionPty lpty rpty x -> Either (lpty x) (rpty x)
invUnionRule = id

public export
0 invUnionLeftRule : UnionPty lpty rpty x -> Not (rpty x) -> lpty x
invUnionLeftRule eprf rcontra = case eprf of
  Left lprf => lprf
  Right rprf => void (rcontra rprf)

public export
0 invUnionRightRule : UnionPty lpty rpty x -> Not (lpty x) -> rpty x
invUnionRightRule eprf lcontra = case eprf of
  Left lprf => void (lcontra lprf)
  Right rprf => rprf

public export
0 invUnionNotLeftRule : Not (UnionPty lpty rpty x) -> Not (lpty x)
invUnionNotLeftRule econtra prf = econtra (Left prf)

public export
invUnionNotLeftElem : DisprovenElem (UnionPty lpty rpty) -> DisprovenElem lpty
invUnionNotLeftElem = projectElem (invUnionNotLeftRule {lpty} {rpty})

public export
0 invUnionNotRightRule : Not (UnionPty lpty rpty x) -> Not (rpty x)
invUnionNotRightRule econtra prf = econtra (Right prf)

public export
invUnionNotRightElem : DisprovenElem (UnionPty lpty rpty) -> DisprovenElem rpty
invUnionNotRightElem = projectElem (invUnionNotRightRule {lpty} {rpty})
