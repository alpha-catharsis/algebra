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
interRule : {x : a} -> {s : Set a} -> {s' : Set a} -> fst s x ->
            fst s' x -> fst (inter s s') x
interRule prf prf' = (prf, prf')

public export
interNotLeftRule : {x : a} -> {s : Set a} -> {s' : Set a} ->
                   (fst s x -> Void) -> fst (inter s s') x -> Void
interNotLeftRule contra = contra . fst

public export
interNotRightRule : {x : a} -> {s : Set a} -> {s' : Set a} ->
                    (fst s' x -> Void) -> fst (inter s s') x -> Void
interNotRightRule contra = contra . snd

public export
invLeftInterRule : {x : a} -> {s : Set a} -> {s' : Set a} ->
                   fst (inter s s') x -> fst s x
invLeftInterRule (prf, _) = prf

public export
invRightInterRule : {x : a} -> {s : Set a} -> {s' : Set a} ->
                    fst (inter s s') x -> fst s' x
invRightInterRule (_, prf') = prf'

public export
invInterNotLeftRule : {x : a} -> {s : Set a} -> {s' : Set a} ->
                      (fst (inter s s') x -> Void) -> (fst s' x) ->
                      fst s x -> Void
invInterNotLeftRule contra prf' prf = void (contra (prf, prf'))

public export
invInterNotRightRule : {x : a} -> {s : Set a} -> {s' : Set a} ->
                       (fst (inter s s') x -> Void) -> (fst s x) ->
                       fst s' x -> Void
invInterNotRightRule contra prf prf' = void (contra (prf, prf'))
