---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Fn.Id

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Fn.Fn
import Alpha.Algebra.Fn.Prop
import Alpha.Algebra.Set.Set

--------------------
-- Identity function
--------------------

public export
fnId : Fn s s
fnId = id

-------------------------------
-- Identity function properties
-------------------------------

public export
fnIdInjective : FnInjective Id.fnId
fnIdInjective _ _ Refl = Refl

public export
fnIdSurjective : FnSurjective Id.fnId
fnIdSurjective y = (y ** Refl)

public export
fnIdBijective : FnBijective Id.fnId
fnIdBijective = (fnIdInjective,fnIdSurjective)
