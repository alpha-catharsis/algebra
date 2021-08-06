---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Function.NullryFn

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

-------------------
-- Nullary function
-------------------

public export
NullryFn : {a : Type} -> (fpt : SetFpt a) -> Type
NullryFn fpt = (a ** fpt a)
