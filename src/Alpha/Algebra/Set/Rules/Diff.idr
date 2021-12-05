---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Diff

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Rules.Compl
import Alpha.Algebra.Set.Rules.Inter
import Alpha.Algebra.Set.Ops
import Alpha.Algebra.Set.Set

-------------------
-- Difference rules
-------------------

public export
0 diffRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} -> SetPrf ls x ->
             Not (SetPrf rs x) -> DiffPrf ls rs x
diffRule lprf rcontra = interRule {rs=compl rs} lprf rcontra

public export
0 diffNotLeftRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                    Not (SetPrf ls x) -> Not (DiffPrf ls rs x)
diffNotLeftRule lcontra = interNotLeftRule {rs=compl rs} lcontra

public export
diffNotLeftElem : Set lt a => Set rt a => {0 ls : lt} -> {0 rs : rt} ->
                  DisprovenElem (SetPrf ls) -> DisprovenElem (DiffPrf ls rs)
diffNotLeftElem = projectElem diffNotLeftRule

public export
0 diffNotRightRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                     SetPrf rs x -> Not (DiffPrf ls rs x)
diffNotRightRule rprf = interNotRightRule {rs=compl rs} (dblComplRule {s=rs}
                                                         rprf)

public export
diffNotRightElem : Set lt a => Set rt a => {0 ls : lt} -> {0 rs : rt} ->
                   ProvenElem (SetPrf rs) -> DisprovenElem (DiffPrf ls rs)
diffNotRightElem = projectElem diffNotRightRule

public export
0 invDiffLeftRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                    DiffPrf ls rs x -> SetPrf ls x
invDiffLeftRule pprf = invInterLeftRule {rs=compl rs} pprf

public export
invDiffLeftElem : Set lt a => Set rt a => {0 ls : lt} -> {0 rs : rt} ->
                  ProvenElem (DiffPrf ls rs) -> ProvenElem (SetPrf ls)
invDiffLeftElem = projectElem invDiffLeftRule

public export
0 invDiffRightRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                     Not (DiffPrf ls rs x) -> SetPrf ls x -> SetPrf rs x
invDiffRightRule pcontra lprf = invDblComplRule (invInterNotRightRule
                                                 {rs=compl rs} pcontra lprf)

public export
0 invDiffNotLeftRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                       Not (DiffPrf ls rs x) -> Not (SetPrf rs x) ->
                       Not (SetPrf ls x)
invDiffNotLeftRule pcontra rcontra = invInterNotLeftRule {rs=compl rs}
                                     pcontra rcontra

public export
0 invDiffNotRightRule : Set lt a => Set rt a => {ls : lt} -> {rs : rt} ->
                        DiffPrf ls rs x -> Not (SetPrf rs x)
invDiffNotRightRule pprf = invInterRightRule {rs=compl rs} pprf

public export
invDiffNotRightElem : Set lt a => Set rt a => {0 ls : lt} -> {0 rs : rt} ->
                      ProvenElem (DiffPrf ls rs) -> DisprovenElem (SetPrf rs)
invDiffNotRightElem = projectElem invDiffNotRightRule
