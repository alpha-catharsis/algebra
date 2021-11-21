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

-- public export
-- 0 diffRule : SetPrf ls x -> SetContra rs x -> SetPrf (diff ls rs) x
-- diffRule lprf rcontra = interRule {rs=compl rs} lprf (complRule rcontra)


-- public export
-- 0 diffNotLeftRule : SetContra ls x -> SetContra (diff ls rs) x
-- diffNotLeftRule lcontra = interNotLeftRule {rs=compl rs} lcontra

-- public export
-- 0 diffNotRightRule : SetPrf rs x -> SetContra (diff ls rs) x
-- diffNotRightRule rprf = interNotRightRule {rs=compl rs} (complNotRule rprf)

-- public export
-- 0 invDiffLeftRule : SetPrf (diff ls rs) x -> SetPrf ls x
-- invDiffLeftRule lprf = invInterLeftRule {rs=compl rs} lprf

-- public export
-- 0 invDiffRightRule : SetContra (diff ls rs) x -> SetPrf ls x -> SetPrf rs x
-- invDiffRightRule pcontra lprf = invDblComplRule (invInterNotRightRule
--                                                  {rs=compl rs} pcontra lprf)

-- public export
-- 0 invDiffNotLeftRule : SetContra (diff ls rs) x -> SetContra rs x ->
--                        SetContra ls x
-- invDiffNotLeftRule pcontra rcontra = invInterNotLeftRule {rs=compl rs}
--                                      pcontra rcontra

-- public export
-- 0 invDiffNotRightRule : SetPrf (diff ls rs) x -> SetContra rs x
-- invDiffNotRightRule pprf = invComplNotRule
--                            (invInterRightRule {rs=compl rs} pprf)
