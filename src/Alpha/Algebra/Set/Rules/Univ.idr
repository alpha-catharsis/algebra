---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Univ

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Incl
import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.Univ

-------------------------
-- Universe set inclusion
-------------------------

public export
0 inclUniv : InclRel a (ls,UnivSet)
inclUniv _ = ()
