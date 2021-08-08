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
NullryFn : {a : Type} -> (s : Set a) -> Type
NullryFn s = (x ** Elem x s)
