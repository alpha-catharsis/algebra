---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Univ

-------------------
-- Internal imports
-------------------

import public Alpha.Algebra.Set.Set

---------------
-- Universe set
---------------

public export
UnivSet : Set a
UnivSet _ = ()

public export
univ : DecSet UnivSet
univ _ = Yes ()

public export
univProvenElem : (x : a) -> ProvenElem {a} UnivSet
univProvenElem x = MkProvenElem x ()
