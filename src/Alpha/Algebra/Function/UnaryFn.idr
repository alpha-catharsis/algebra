---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Function.UnaryFn

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

-------------------
-- Nullary function
-------------------

public export
UnaryFn : {a : Type} -> {b : Type} -> (ls : Set a) -> (rs : Set b) -> Type
UnaryFn ls rs = (x ** Elem x ls) -> (y ** Elem y rs)
