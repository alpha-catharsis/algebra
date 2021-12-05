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
0 unionLeftRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                  SetPrf ls x -> UnionPrf ls rs x
unionLeftRule = Left

public export
unionLeftElem : Set lt a => Set rt a => {0 ls : lt} -> {0 rs : rt} ->
                ProvenElem (SetPrf ls) -> ProvenElem (UnionPrf ls rs)
unionLeftElem = projectElem unionLeftRule

public export
0 unionRightRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                   SetPrf rs x -> UnionPrf ls rs x
unionRightRule = Right

public export
unionRightElem : Set lt a => Set rt a => {0 ls : lt} -> {0 rs : rt} ->
               ProvenElem (SetPrf rs) -> ProvenElem (UnionPrf ls rs)
unionRightElem = projectElem unionRightRule

public export
0 unionNotRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                 Not (SetPrf ls x) -> Not (SetPrf rs x) ->
                 Not (UnionPrf ls rs x)
unionNotRule lcontra rcontra eprf = case eprf of
  Left lprf => lcontra lprf
  Right rprf => rcontra rprf

public export
0 invUnionRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                 UnionPrf ls rs x -> Either (SetPrf ls x) (SetPrf rs x)
invUnionRule = id

public export
0 invUnionLeftRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                     UnionPrf ls rs x -> Not (SetPrf rs x) -> SetPrf ls x
invUnionLeftRule eprf rcontra = case eprf of
  Left lprf => lprf
  Right rprf => void (rcontra rprf)

public export
0 invUnionRightRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                      UnionPrf ls rs x -> Not (SetPrf ls x) -> SetPrf rs x
invUnionRightRule eprf lcontra = case eprf of
  Left lprf => void (lcontra lprf)
  Right rprf => rprf

public export
0 invUnionNotLeftRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                        Not (UnionPrf ls rs x) -> Not (SetPrf ls x)
invUnionNotLeftRule econtra prf = econtra (Left prf)

public export
invUnionNotLeftElem : Set lt a => Set rt a => {0 ls : lt} -> {0 rs : rt} ->
                      DisprovenElem (UnionPrf ls rs) ->
                      DisprovenElem (SetPrf ls)
invUnionNotLeftElem = projectElem invUnionNotLeftRule

public export
0 invUnionNotRightRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                         Not (UnionPrf ls rs x) -> Not (SetPrf rs x)
invUnionNotRightRule econtra prf = econtra (Right prf)

public export
invUnionNotRightElem : Set lt a => Set rt a => {0 ls : lt} -> {0 rs : rt} ->
                       DisprovenElem (UnionPrf ls rs) ->
                       DisprovenElem (SetPrf rs)
invUnionNotRightElem = projectElem invUnionNotRightRule
