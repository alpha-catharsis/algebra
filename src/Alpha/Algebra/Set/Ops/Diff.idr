---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Ops.Diff

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Ops.Compl
import Alpha.Algebra.Set.Ops.Inter
import Alpha.Algebra.Set.Empty
import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.Univ
import Alpha.Decidable

-------------
-- Difference
-------------

public export
Diff : Set a -> Set a -> Set a
Diff ls rs = Inter ls (Compl rs)

public export
diff : DecSet ls -> DecSet rs -> DecSet (Diff ls rs)
diff ls rs = inter ls (compl rs)
