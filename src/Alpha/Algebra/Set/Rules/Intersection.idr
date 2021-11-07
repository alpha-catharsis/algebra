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
interRule : {x : a} -> {ls : Set a} -> {rs : Set a} -> setPrf ls x ->
            setPrf rs x -> setPrf (inter ls rs) x
interRule lprf rprf = (lprf, rprf)

public export
interNotLeftRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                   (setPrf ls x -> Void) -> setPrf (inter ls rs) x -> Void
interNotLeftRule lcontra = lcontra . fst

public export
interNotRightRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                    (setPrf rs x -> Void) -> setPrf (inter ls rs) x -> Void
interNotRightRule rcontra = rcontra . snd

public export
invLeftInterRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                   setPrf (inter ls rs) x -> setPrf ls x
invLeftInterRule (lprf, _) = lprf

public export
invRightInterRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                    setPrf (inter ls rs) x -> setPrf rs x
invRightInterRule (_, rprf) = rprf

public export
invInterNotLeftRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                      (setPrf (inter ls rs) x -> Void) -> (setPrf rs x) ->
                      setPrf ls x -> Void
invInterNotLeftRule pcontra rprf lprf = void (pcontra (lprf, rprf))

public export
invInterNotRightRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                       (setPrf (inter ls rs) x -> Void) -> (setPrf ls x) ->
                       setPrf rs x -> Void
invInterNotRightRule pcontra lprf rprf = void (pcontra (lprf, rprf))
