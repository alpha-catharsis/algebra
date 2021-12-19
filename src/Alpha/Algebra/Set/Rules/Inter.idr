---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Inter

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Ops
import Alpha.Algebra.Set.Set

--------------
-- Basic rules
--------------

public export
0 interRule : (ls : Set a) -> (rs : Set a) -> ls x -> rs x -> Inter ls rs x
interRule _ _ lprf rprf = (lprf, rprf)

public export
0 interNotLeftRule : (ls : Set a) -> (rs : Set a) -> Not (ls x) -> Not (Inter ls rs x)
interNotLeftRule _ _ lcontra = lcontra . fst

public export
0 interNotRightRule : (ls : Set a) -> (rs : Set a) -> Not (rs x) -> Not (Inter ls rs x)
interNotRightRule _ _ rcontra = rcontra . snd

public export
0 invInterLeftRule : (ls : Set a) -> (rs : Set a) -> Inter ls rs x -> ls x
invInterLeftRule _ _ = fst

public export
0 invInterRightRule : (ls : Set a) -> (rs : Set a) -> Inter ls rs x -> rs x
invInterRightRule _ _ = snd

public export
0 invInterNotLeftRule : (ls : Set a) -> (rs : Set a) -> Not (Inter ls rs x) -> rs x -> Not (ls x)
invInterNotLeftRule _ _ pcontra rprf lprf = void (pcontra (lprf, rprf))

public export
0 invInterNotRightRule : (ls : Set a) -> (rs : Set a) -> Not (Inter ls rs x) -> ls x -> Not (rs x)
invInterNotRightRule _ _ pcontra lprf rprf = void (pcontra (lprf, rprf))

----------------------
-- Basic element rules
----------------------

public export
interNotLeftElem : DisprovenElem ls -> DisprovenElem (Inter ls rs)
interNotLeftElem = projectElem (interNotLeftRule ls rs)

public export
interNotRightElem : DisprovenElem rs -> DisprovenElem (Inter ls rs)
interNotRightElem = projectElem (interNotRightRule ls rs)

public export
invInterLeftElem : ProvenElem (Inter ls rs) -> ProvenElem ls
invInterLeftElem = projectElem (invInterLeftRule ls rs)

public export
invInterRightElem : ProvenElem (Inter ls rs) -> ProvenElem rs
invInterRightElem = projectElem (invInterRightRule ls rs)
