---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.DerivedOps

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.BasicOps

-----------------
-- Set difference
-----------------

public export
Difference : Set a -> Set a -> Set a
Difference ls rs = Intersection ls (Complement rs)

public export
difference : SetDec ls -> SetDec rs -> SetDec (Difference ls rs)
difference lf rf = intersection lf (complement rf)


export
elemDifference : Elem x ls -> NotElem x rs ->
                 Elem x (Difference ls rs)
elemDifference lprf rcontra = (lprf, rcontra)

export
notElemDifferenceLeft : NotElem x ls -> NotElem x (Difference ls _)
notElemDifferenceLeft lcontra (lprf,_) = lcontra lprf

export
notElemDifferenceRight : Elem x rs -> NotElem x (Difference _ rs)
notElemDifferenceRight rprf contra = snd contra rprf

---------------------------
-- Set symmetric difference
---------------------------

public export
SymDifference : Set a -> Set a -> Set a
SymDifference ls rs = Union (Difference ls rs) (Difference rs ls)

public export
symDifference : SetDec ls -> SetDec rs -> SetDec (SymDifference ls rs)
symDifference lf rf = union (difference lf rf) (difference rf lf)


export
elemDifferenceLeft : Elem x ls -> NotElem x rs ->
                     Elem x (SymDifference ls rs)
elemDifferenceLeft lprf rcontra = Left (lprf, rcontra)

export
elemDifferenceRight : NotElem x ls -> Elem x rs ->
                      Elem x (SymDifference ls rs)
elemDifferenceRight lcontra rprf = Right (rprf, lcontra)

export
notElemDifferenceBoth : Elem x ls -> Elem x rs ->
                        NotElem x (SymDifference ls rs)
notElemDifferenceBoth lprf rprf econtra = case econtra of
  Left (_,rcontra) => rcontra rprf
  Right (_, lcontra) => lcontra lprf

export
notElemDifferenceNeither : NotElem x ls -> NotElem x rs ->
                           NotElem x (SymDifference ls rs)
notElemDifferenceNeither lcontra rcontra econtra = case econtra of
  Left (lprf, _) => lcontra lprf
  Right (rprf, _) => rcontra rprf
