---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Inter

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Ops
import Alpha.Algebra.Set.Set

---------------------
-- Intersection rules
---------------------

-- public export
-- 0 interRule : SetPrf ls x -> SetPrf rs x -> SetPrf (inter ls rs) x
-- interRule lprf rprf = (lprf, rprf)

-- public export
-- 0 interNotLeftRule : SetContra ls x -> SetContra (inter ls rs) x
-- interNotLeftRule lcontra = lcontra . fst

-- public export
-- 0 interNotRightRule : SetContra rs x -> SetContra (inter ls rs) x
-- interNotRightRule rcontra = rcontra . snd

-- public export
-- 0 invInterLeftRule : SetPrf (inter ls rs) x -> SetPrf ls x
-- invInterLeftRule = fst

-- public export
-- 0 invInterRightRule : SetPrf (inter ls rs) x -> SetPrf rs x
-- invInterRightRule = snd

-- public export
-- 0 invInterNotLeftRule : SetContra (inter ls rs) x -> SetPrf rs x ->
--                         SetContra ls x
-- invInterNotLeftRule pcontra rprf lprf = void (pcontra (lprf, rprf))

-- public export
-- 0 invInterNotRightRule : SetContra (inter ls rs) x -> SetPrf ls x ->
--                          SetContra rs x
-- invInterNotRightRule pcontra lprf rprf = void (pcontra (lprf, rprf))
