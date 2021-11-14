---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Inclusion

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Set.Basic
import Alpha.Algebra.Set.Rules.Complement
import Alpha.Algebra.Set.Set

-----------------------
-- Inclusion definition
-----------------------

-- public export
-- InclPrf : {a : Type} -> RelPrf (Set a) (Set a)
-- InclPrf (ls,rs) = ((x : a) -> setPrf ls x -> setPrf rs x)

-- public export
-- inclRefl : RelRefl InclPrf
-- inclRefl ls = \_,prf => prf

-- public export
-- inclTrans : RelTrans


-- public export
-- inclUniv : {a : Type} -> (ls : Set a) -> InclPrf (ls, univ {a})
-- inclUniv ls = \_,_ => ()

-- public export
-- inclEmpty : {a : Type} -> (rs : Set a) -> InclPrf (Basic.empty {a}, rs)
-- inclEmpty rs = \x,prf => void (complNotRule {x} {s=univ} () prf)
