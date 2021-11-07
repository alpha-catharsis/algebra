---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Difference

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Rules.Complement
import Alpha.Algebra.Set.Rules.Intersection
import Alpha.Algebra.Set.Ops
import Alpha.Algebra.Set.Set

-------------------
-- Difference rules
-------------------

public export
diffRule : {x : a} -> {ls : Set a} -> {rs : Set a} -> setPrf ls x ->
           (setPrf rs x -> Void) -> setPrf (diff ls rs) x
diffRule lprf rcontra = interRule {rs=compl rs} lprf (complRule rcontra)

public export
diffNotLeftRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                  (setPrf ls x -> Void) -> setPrf (diff ls rs) x -> Void
diffNotLeftRule lcontra = interNotLeftRule {rs=compl rs} lcontra

public export
diffNotRightRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                   setPrf rs x -> setPrf (diff ls rs) x -> Void
diffNotRightRule rprf = interNotRightRule {rs=compl rs} (complNotRule rprf)

public export
invDiffLeftRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                  setPrf (diff ls rs) x -> setPrf ls x
invDiffLeftRule lprf = invLeftInterRule {rs=compl rs} lprf

public export
invDiffRightRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                   (setPrf (diff ls rs) x -> Void) -> setPrf ls x ->
                   setPrf rs x
invDiffRightRule pcontra lprf = invDblComplRule (invInterNotRightRule
                                                 {rs=compl rs} pcontra lprf)

public export
invDiffNotLeftRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                     (setPrf (diff ls rs) x -> Void) ->
                     (setPrf rs x -> Void) -> setPrf ls x -> Void
invDiffNotLeftRule pcontra rcontra = invInterNotLeftRule {rs=compl rs}
                                     pcontra rcontra

public export
invDiffNotRightRule : {x : a} -> {ls : Set a} -> {rs : Set a} ->
                      setPrf (diff ls rs) x -> setPrf rs x -> Void
invDiffNotRightRule pprf = invComplNotRule
                           (invRightInterRule pprf {rs=compl rs})
