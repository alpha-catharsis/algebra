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
difference : Set lfpt a -> Set rfpt a -> Set (\x => (lfpt x, Not (rfpt x))) a
difference ls rs = intersection ls (complement rs)

public export
elemDifference : {0 rfpt : a -> Type} -> {x : a} -> {ls : Set lfpt a} ->
                 {rs : Set rfpt a} -> Elem x ls -> (Elem x rs -> Void) ->
                 Elem x (difference ls rs)
elemDifference lprf rcontra = elemIntersection lprf (elemComplement rcontra)

public export
notElemDifferenceLeft : {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} ->
                        (Elem x ls -> Void) -> Elem x (difference ls rs) ->
                        Void
notElemDifferenceLeft lcontra = notElemIntersectionLeft lcontra

public export
notElemDifferenceRight : {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} ->
                         Elem x rs -> Elem x (difference ls rs) -> Void
notElemDifferenceRight rprf = notElemIntersectionRight (notElemComplement rprf)

public export
symDifference : {lfpt : a -> Type} -> Set lfpt a -> Set rfpt a ->
                Set (\x => Either (lfpt x, Not (rfpt x))
                                  (rfpt x , Not (lfpt x))) a
symDifference ls rs = union (difference ls rs) (difference rs ls)

---------------------------
-- Set symmetric difference
---------------------------

public export
elemSymDifferenceLeft : {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} ->
                        Elem x ls -> (Elem x rs -> Void) ->
                        Elem x (symDifference ls rs)
elemSymDifferenceLeft lprf rcontra = elemUnionLeft
                                     (elemDifference lprf rcontra)

public export
elemSymDifferenceRight : {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} ->
                         (Elem x ls -> Void) -> Elem x rs ->
                         Elem x (symDifference ls rs)
elemSymDifferenceRight lcontra rprf = elemUnionRight
                                      (elemDifference rprf lcontra)

public export
notElemSymDifferenceBoth : {x : a} -> {ls : Set lfpt a} -> {rs : Set rfpt a} ->
                           Elem x ls -> Elem x rs ->
                           Elem x (symDifference ls rs) -> Void
notElemSymDifferenceBoth lprf rprf = notElemUnion (notElemDifferenceRight rprf)
                                     (notElemDifferenceRight lprf)

public export
notElemSymDifferenceBothNot : {x : a} -> {ls : Set lfpt a} ->
                              {rs : Set rfpt a} -> (Elem x ls -> Void) ->
                              (Elem x rs -> Void) ->
                              Elem x (symDifference ls rs) -> Void
notElemSymDifferenceBothNot lprf rprf = notElemUnion
                                        (notElemDifferenceLeft lprf)
                                        (notElemDifferenceLeft rprf)
