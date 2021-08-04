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
DifferencePrf : SetFpt a -> SetFpt a -> SetFpt a
DifferencePrf lfpt rfpt = IntersectionPrf lfpt (ComplementPrf rfpt)

public export
difference : SetFn lfpt -> SetFn rfpt -> SetFn (DifferencePrf lfpt rfpt)
difference lf rf = intersection lf (complement rf)


export
elemDifference : SetPrf lfpt x -> SetContra rfpt x ->
                 SetPrf (DifferencePrf lfpt rfpt) x
elemDifference lprf rcontra = (lprf, rcontra)

export
notElemDifferenceLeft : SetContra lfpt x -> SetContra (DifferencePrf lfpt _) x
notElemDifferenceLeft lcontra (lprf,_) = lcontra lprf

export
notElemDifferenceRight : SetPrf rfpt x -> SetContra (DifferencePrf _ rfpt) x
notElemDifferenceRight rprf contra = snd contra rprf

---------------------------
-- Set symmetric difference
---------------------------

public export
SymDifferencePrf : SetFpt a -> SetFpt a -> SetFpt a
SymDifferencePrf lfpt rfpt = UnionPrf (DifferencePrf lfpt rfpt)
                             (DifferencePrf rfpt lfpt)

public export
symDifference : SetFn lfpt -> SetFn rfpt -> SetFn (SymDifferencePrf lfpt rfpt)
symDifference lf rf = union (difference lf rf) (difference rf lf)


export
elemDifferenceLeft : SetPrf lfpt x -> SetContra rfpt x ->
                     SetPrf (SymDifferencePrf lfpt rfpt) x
elemDifferenceLeft lprf rcontra = Left (lprf, rcontra)

export
elemDifferenceRight : SetContra lfpt x -> SetPrf rfpt x ->
                      SetPrf (SymDifferencePrf lfpt rfpt) x
elemDifferenceRight lcontra rprf = Right (rprf, lcontra)

export
notElemDifferenceBoth : SetPrf lfpt x -> SetPrf rfpt x ->
                        SetContra (SymDifferencePrf lfpt rfpt) x
notElemDifferenceBoth lprf rprf econtra = case econtra of
  Left (_,rcontra) => rcontra rprf
  Right (_, lcontra) => lcontra lprf

export
notElemDifferenceNeither : SetContra lfpt x -> SetContra rfpt x ->
                           SetContra (SymDifferencePrf lfpt rfpt) x
notElemDifferenceNeither lcontra rcontra econtra = case econtra of
  Left (lprf, _) => lcontra lprf
  Right (rprf, _) => rcontra rprf
