---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Union

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Rel.Incl
import Alpha.Algebra.Rel.SetEq
import Alpha.Algebra.Set.Ops.Compl
import Alpha.Algebra.Set.Ops.Union
import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.Empty
import Alpha.Algebra.Set.Univ

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

-------------------
-- Union equalities
-------------------

0 setEqUnionLeftUniv : SetEqRel a (UnivSet, Union UnivSet rs)
setEqUnionLeftUniv = (Left, \eprf => case eprf of
  Left lprf => lprf
  Right _ => ())

0 setEqUnionRightUnion : SetEqRel a (UnivSet, Union ls UnivSet)
setEqUnionRightUnion = (Right, \eprf => case eprf of
  Left _ => ()
  Right rprf => rprf)

0 setEqUnionLeftEmpty : SetEqRel a (rs, Union EmptySet rs)
setEqUnionLeftEmpty = (Right, \eprf => case eprf of
  Left lprf => absurd lprf
  Right rprf => rprf)

0 setEqUnionRightEmpty : SetEqRel a (ls, Union ls EmptySet)
setEqUnionRightEmpty = (Left, \eprf => case eprf of
  Left lprf => lprf
  Right rprf => absurd rprf)

0 setEqUnionSelf : SetEqRel a (s, Union s s)
setEqUnionSelf = (Left, \eprf => case eprf of
  Left lprf => lprf
  Right rprf => rprf)
