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
-- Basic rules
--------------

public export
0 unionLeftRule : (ls : Set a) -> (rs : Set a) -> ls x -> Union ls rs x
unionLeftRule _ _ = Left

public export
0 unionRightRule : (ls : Set a) -> (rs : Set a) -> rs x -> Union ls rs x
unionRightRule _ _ = Right

public export
0 unionNotRule : (ls : Set a) -> (rs : Set a) -> Not (ls x) -> Not (rs x) -> Not (Union ls rs x)
unionNotRule _ _ lcontra rcontra eprf = case eprf of
  Left lprf => lcontra lprf
  Right rprf => rcontra rprf

public export
0 invUnionRule : (ls : Set a) -> (rs : Set a) -> Union ls rs x -> Either (ls x) (rs x)
invUnionRule _ _ = id

public export
0 invUnionLeftRule : (ls : Set a) -> (rs : Set a) -> Union ls rs x -> Not (rs x) -> ls x
invUnionLeftRule _ _ eprf rcontra = case eprf of
  Left lprf => lprf
  Right rprf => void (rcontra rprf)

public export
0 invUnionRightRule : (ls : Set a) -> (rs : Set a) -> Union ls rs x -> Not (ls x) -> rs x
invUnionRightRule _ _ eprf lcontra = case eprf of
  Left lprf => void (lcontra lprf)
  Right rprf => rprf

public export
0 invUnionNotLeftRule : (ls : Set a) -> (rs : Set a) -> Not (Union ls rs x) -> Not (ls x)
invUnionNotLeftRule _ _ econtra prf = econtra (Left prf)

public export
0 invUnionNotRightRule : (ls : Set a) -> (rs : Set a) -> Not (Union ls rs x) -> Not (rs x)
invUnionNotRightRule _ _ econtra prf = econtra (Right prf)

----------------------
-- Basic element rules
----------------------

public export
unionLeftElem : ProvenElem ls -> ProvenElem (Union ls rs)
unionLeftElem = projectElem (unionLeftRule ls rs)

public export
unionRightElem : ProvenElem rs -> ProvenElem (Union ls rs)
unionRightElem = projectElem (unionRightRule ls rs)

public export
invUnionNotLeftElem : DisprovenElem (Union ls rs) -> DisprovenElem ls
invUnionNotLeftElem = projectElem (invUnionNotLeftRule ls rs)

public export
invUnionNotRightElem : DisprovenElem (Union ls rs) -> DisprovenElem rs
invUnionNotRightElem = projectElem (invUnionNotRightRule ls rs)
