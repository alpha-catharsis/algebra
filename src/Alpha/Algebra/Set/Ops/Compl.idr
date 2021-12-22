---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Ops.Compl

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.Univ
import Alpha.Decidable

-------------
-- Complement
-------------

public export
Compl : Set a -> Set a
Compl s = Not . s

public export
compl : DecSet s -> DecSet (Compl s)
compl s x = decNot (isElem x s)

