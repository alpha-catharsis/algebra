---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Basic

-------------------
-- Internal imports
-------------------

import public Alpha.Algebra.Set.Ops
import public Alpha.Algebra.Set.Set

---------------
-- Universe set
---------------

public export
univ : Set a
univ = (const () ** const (Yes ()))

public export
univProven : a -> ProvenElem (univ {a})
univProven x = (x ** ())

------------
-- Empty set
------------

public export
empty : Set a
empty = compl univ
