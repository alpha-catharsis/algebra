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
DifferenceFpt : SetFpt a -> SetFpt a -> SetFpt a
DifferenceFpt lfpt rfpt = IntersectionFpt lfpt (ComplementFpt rfpt)

public export
difference : Set lfpt -> Set rfpt -> Set (DifferenceFpt lfpt rfpt)
difference lf rf = intersection lf (complement rf)


export
elemDifference : Elem x lfpt -> NotElem x rfpt ->
                 Elem x (DifferenceFpt lfpt rfpt)
elemDifference lprf rcontra = (lprf, rcontra)

export
notElemDifferenceLeft : NotElem x lfpt -> NotElem x (DifferenceFpt lfpt _)
notElemDifferenceLeft lcontra (lprf,_) = lcontra lprf

export
notElemDifferenceRight : Elem x rfpt -> NotElem x (DifferenceFpt _ rfpt)
notElemDifferenceRight rprf contra = snd contra rprf

---------------------------
-- Set symmetric difference
---------------------------

public export
SymDifferenceFpt : SetFpt a -> SetFpt a -> SetFpt a
SymDifferenceFpt lfpt rfpt = UnionFpt (DifferenceFpt lfpt rfpt)
                             (DifferenceFpt rfpt lfpt)

public export
symDifference : Set lfpt -> Set rfpt -> Set (SymDifferenceFpt lfpt rfpt)
symDifference lf rf = union (difference lf rf) (difference rf lf)


export
elemDifferenceLeft : Elem x lfpt -> NotElem x rfpt ->
                     Elem x (SymDifferenceFpt lfpt rfpt)
elemDifferenceLeft lprf rcontra = Left (lprf, rcontra)

export
elemDifferenceRight : NotElem x lfpt -> Elem x rfpt ->
                      Elem x (SymDifferenceFpt lfpt rfpt)
elemDifferenceRight lcontra rprf = Right (rprf, lcontra)

export
notElemDifferenceBoth : Elem x lfpt -> Elem x rfpt ->
                        NotElem x (SymDifferenceFpt lfpt rfpt)
notElemDifferenceBoth lprf rprf econtra = case econtra of
  Left (_,rcontra) => rcontra rprf
  Right (_, lcontra) => lcontra lprf

export
notElemDifferenceNeither : NotElem x lfpt -> NotElem x rfpt ->
                           NotElem x (SymDifferenceFpt lfpt rfpt)
notElemDifferenceNeither lcontra rcontra econtra = case econtra of
  Left (lprf, _) => lcontra lprf
  Right (rprf, _) => rcontra rprf
