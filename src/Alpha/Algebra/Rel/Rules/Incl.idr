---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Rules.Incl

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Incl
import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Rel.Prop
import Alpha.Algebra.Rel.SetEq
import Alpha.Algebra.Set.Basic
import Alpha.Algebra.Set.Set

-------------------------
-- Universe set inclusion
-------------------------

-- public export
-- 0 inclUniv : Set lt a => {ls : lt} -> InclPrf (ls,MkUniv)
-- inclUniv _ _ = ()

----------------------
-- Empty set inclusion
----------------------

-- public export
-- 0 inclEmpty : Set rt a => {rs : rt} -> InclPrf (MkEmpty,rs)
-- inclEmpty _ _ impossible
