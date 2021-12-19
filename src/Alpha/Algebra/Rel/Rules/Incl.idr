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

public export
0 inclUniv : InclRel a (ls,UnivSet)
inclUniv _ = ()

----------------------
-- Empty set inclusion
----------------------

public export
0 inclEmpty : InclRel a (EmptySet,rs)
inclEmpty (_,_) impossible
