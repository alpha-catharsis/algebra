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

public export
nullryFn : {a : Type} -> (s : Set a) -> (x : a) -> {auto prf : Elem x s} ->
           NullryFn s
nullryFn s x = (x ** prf)
