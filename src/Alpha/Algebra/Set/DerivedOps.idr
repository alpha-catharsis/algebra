---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.DerivedOps

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.BasicOps
import Alpha.Decidable

-----------------
-- Set difference
-----------------

public export
difference : Set a -> Set a -> Set a
difference ls rs = intersection ls (complement rs)

export
elemDifference : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                 Elem x ls -> (Elem x rs -> Void) ->
                 Elem x (difference ls rs)
elemDifference lprf rcontra = elemIntersection lprf (elemComplement rcontra)

export
notElemDifferenceLeft : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                        (Elem x ls -> Void) -> Elem x (difference ls rs) ->
                        Void
notElemDifferenceLeft lcontra = \(MkElem _ _ (lprf, _)) =>
                                  lcontra (MkElem _ _ lprf)

export
notElemDifferenceRight : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                         Elem x rs -> Elem x (difference ls rs) -> Void
notElemDifferenceRight rprf = notElemIntersectionRight (notElemComplement rprf)

---------------------------
-- Set symmetric difference
---------------------------

public export
symDifference : Set a -> Set a -> Set a
symDifference ls rs = union (difference ls rs) (difference rs ls)

export
elemSymDifferenceLeft : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                        Elem x ls -> (Elem x rs -> Void) ->
                        Elem x (symDifference ls rs)
elemSymDifferenceLeft lprf rcontra = let (MkElem _ _ prf) =
                                         elemDifference lprf rcontra
                                     in MkElem _ _ (Left prf)

export
elemSymDifferenceRight : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                         (Elem x ls -> Void) -> Elem x rs ->
                         Elem x (symDifference ls rs)
elemSymDifferenceRight lcontra rprf = let (MkElem _ _ prf) =
                                        elemDifference rprf lcontra
                                      in MkElem _ _ (Right prf)

export
notElemSymDifferenceBoth : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                           Elem x ls -> Elem x rs ->
                           Elem x (symDifference ls rs) -> Void
notElemSymDifferenceBoth lprf rprf = notElemUnion (notElemDifferenceRight rprf)
                                     (notElemDifferenceRight lprf)

export
notElemSymDifferenceBothNot : {x : a} -> {ls : Set a} ->
                              {rs : Set a} -> (Elem x ls -> Void) ->
                              (Elem x rs -> Void) ->
                              Elem x (symDifference ls rs) -> Void
notElemSymDifferenceBothNot lprf rprf = notElemUnion
                                        (notElemDifferenceLeft lprf)
                                        (notElemDifferenceLeft rprf)
