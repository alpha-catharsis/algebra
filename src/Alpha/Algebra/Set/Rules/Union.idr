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
-- Union rules
--------------

public export
leftUnionRule : {x : a} -> {ls : Set a} -> {rs : Set a} -> setPrf ls x ->
                setPrf (union ls rs) x
leftUnionRule lprf = Left lprf

public export
rightUnionRule : {x : a} -> {ls : Set a} -> {rs : Set a} -> setPrf rs x ->
                 setPrf (union ls rs) x
rightUnionRule rprf = Right rprf

public export
unionNotRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
               (setPrf ls x -> Void) -> (setPrf rs x -> Void) ->
               setPrf (union ls rs) x -> Void
unionNotRule lcontra rcontra eprf = case eprf of
  Left lprf => lcontra lprf
  Right rprf => rcontra rprf

public export
invUnionRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
               setPrf (union ls rs) x ->
               Either (setPrf ls x) (setPrf rs x)
invUnionRule = id

public export
invUnionLeftRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                   setPrf (union ls rs) x -> (setPrf rs x -> Void) ->
                   setPrf ls x
invUnionLeftRule eprf rcontra = case eprf of
  Left lprf => lprf
  Right rprf => void (rcontra rprf)

public export
invUnionRightRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                    setPrf (union ls rs) x -> (setPrf ls x -> Void) ->
                    setPrf rs x
invUnionRightRule eprf lcontra = case eprf of
  Left lprf => void (lcontra lprf)
  Right rprf => rprf

public export
invUnionNotRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                  (setPrf (union ls rs) x -> Void) ->
                  (setPrf ls x, setPrf rs x) -> Void
invUnionNotRule econtra pprf = econtra (Left (fst pprf))
