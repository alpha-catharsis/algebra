---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Intersection

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Ops
import Alpha.Algebra.Set.Set

---------------------
-- Intersection rules
---------------------

public export
0 interRule : SetPrf ls x -> SetPrf rs x -> SetPrf (inter ls rs) x
interRule lprf rprf = (lprf, rprf)

public export
0 interNotLeftRule : (SetPrf ls x -> Void) -> SetPrf (inter ls rs) x -> Void
interNotLeftRule lcontra = lcontra . fst

public export
0 interNotRightRule : (SetPrf rs x -> Void) -> SetPrf (inter ls rs) x -> Void
interNotRightRule rcontra = rcontra . snd

public export
0 invInterLeftRule : SetPrf (inter ls rs) x -> SetPrf ls x
invInterLeftRule = fst

public export
0 invInterRightRule : SetPrf (inter ls rs) x -> SetPrf rs x
invInterRightRule = snd

public export
0 invInterNotLeftRule : (SetPrf (inter ls rs) x -> Void) -> SetPrf rs x ->
                        SetPrf ls x -> Void
invInterNotLeftRule pcontra rprf lprf = void (pcontra (lprf, rprf))

public export
0 invInterNotRightRule : (SetPrf (inter ls rs) x -> Void) -> SetPrf ls x ->
                         SetPrf rs x -> Void
invInterNotRightRule pcontra lprf rprf = void (pcontra (lprf, rprf))
