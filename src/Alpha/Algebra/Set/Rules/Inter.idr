---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Inter

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Ops
import Alpha.Algebra.Set.Set

---------------------
-- Intersection rules
---------------------

public export
0 interRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
              SetPrf ls x -> SetPrf rs x -> InterPrf ls rs x
interRule lprf rprf = (lprf, rprf)

public export
0 interNotLeftRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                     Not (SetPrf ls x) -> Not (InterPrf ls rs x)
interNotLeftRule lcontra = lcontra . fst

public export
interNotLeftElem : Set lt a => Set rt a => {0 ls : lt} -> {0 rs : rt} ->
                   DisprovenElem (SetPrf ls) -> DisprovenElem (InterPrf ls rs)
interNotLeftElem = projectElem interNotLeftRule

public export
0 interNotRightRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                      Not (SetPrf rs x) -> Not (InterPrf ls rs x)
interNotRightRule rcontra = rcontra . snd

public export
interNotRightElem : Set lt a => Set rt a => {0 ls : lt} -> {0 rs : rt} ->
                    DisprovenElem (SetPrf rs) -> DisprovenElem (InterPrf ls rs)
interNotRightElem = projectElem interNotRightRule

public export
0 invInterLeftRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                     InterPrf ls rs x -> SetPrf ls x
invInterLeftRule = fst

public export
invInterLeftElem : Set lt a => Set rt a => {0 ls : lt} -> {0 rs : rt} ->
                   ProvenElem (InterPrf ls rs) -> ProvenElem (SetPrf ls)
invInterLeftElem = projectElem invInterLeftRule

public export
0 invInterRightRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                      InterPrf ls rs x -> SetPrf rs x
invInterRightRule = snd

public export
invInterRightElem : Set lt a => Set rt a => {0 ls : lt} -> {0 rs : rt} ->
                    ProvenElem (InterPrf ls rs) -> ProvenElem (SetPrf rs)
invInterRightElem = projectElem invInterRightRule

public export
0 invInterNotLeftRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                        Not (InterPrf ls rs x) -> SetPrf rs x ->
                        Not (SetPrf ls x)
invInterNotLeftRule pcontra rprf lprf = void (pcontra (lprf, rprf))

public export
0 invInterNotRightRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                         Not (InterPrf ls rs x) -> SetPrf ls x ->
                         Not (SetPrf rs x)
invInterNotRightRule pcontra lprf rprf = void (pcontra (lprf, rprf))
