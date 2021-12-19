---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Empty

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Incl
import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.Empty

----------------------
-- Empty set inclusion
----------------------

public export
0 inclEmpty : InclRel a (EmptySet,rs)
inclEmpty (_,_) impossible
