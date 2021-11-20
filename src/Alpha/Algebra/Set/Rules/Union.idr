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
0 leftUnionRule : SetPrf ls x -> SetPrf (union ls rs) x
leftUnionRule = Left

public export
0 rightUnionRule : SetPrf rs x -> SetPrf (union ls rs) x
rightUnionRule = Right

public export
0 unionNotRule : (SetPrf ls x -> Void) -> (SetPrf rs x -> Void) ->
                 SetPrf (union ls rs) x -> Void
unionNotRule lcontra rcontra eprf = case eprf of
  Left lprf => lcontra lprf
  Right rprf => rcontra rprf

public export
0 invUnionRule : SetPrf (union ls rs) x -> Either (SetPrf ls x) (SetPrf rs x)
invUnionRule = id

public export
0 invUnionLeftRule : SetPrf (union ls rs) x -> (SetPrf rs x -> Void) ->
                     SetPrf ls x
invUnionLeftRule eprf rcontra = case eprf of
  Left lprf => lprf
  Right rprf => void (rcontra rprf)

public export
0 invUnionRightRule : SetPrf (union ls rs) x -> (SetPrf ls x -> Void) ->
                      SetPrf rs x
invUnionRightRule eprf lcontra = case eprf of
  Left lprf => void (lcontra lprf)
  Right rprf => rprf

public export
0 invUnionNotRule : (SetPrf (union ls rs) x -> Void) ->
                    (SetPrf ls x, SetPrf rs x) -> Void
invUnionNotRule econtra prf = econtra (Left (fst prf))
