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

-- public export
-- 0 leftUnionRule : SetPrf ls x -> SetPrf (union ls rs) x
-- leftUnionRule = Left

-- public export
-- 0 rightUnionRule : SetPrf rs x -> SetPrf (union ls rs) x
-- rightUnionRule = Right

-- public export
-- 0 unionNotRule : SetContra ls x -> SetContra rs x -> SetContra (union ls rs) x
-- unionNotRule lcontra rcontra eprf = case eprf of
--   Left lprf => lcontra lprf
--   Right rprf => rcontra rprf

-- public export
-- 0 invUnionRule : SetPrf (union ls rs) x -> Either (SetPrf ls x) (SetPrf rs x)
-- invUnionRule = id

-- public export
-- 0 invUnionLeftRule : SetPrf (union ls rs) x -> SetContra rs x -> SetPrf ls x
-- invUnionLeftRule eprf rcontra = case eprf of
--   Left lprf => lprf
--   Right rprf => void (rcontra rprf)

-- public export
-- 0 invUnionRightRule : SetPrf (union ls rs) x -> SetContra ls x -> SetPrf rs x
-- invUnionRightRule eprf lcontra = case eprf of
--   Left lprf => void (lcontra lprf)
--   Right rprf => rprf

-- public export
-- 0 invUnionNotRule : SetContra (union ls rs) x -> Not (SetPrf ls x, SetPrf rs x)
-- invUnionNotRule econtra prf = econtra (Left (fst prf))
