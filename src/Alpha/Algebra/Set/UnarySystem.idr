---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.UnarySystem

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Function.UnaryFn
import Alpha.Algebra.Set.Set

---------------
-- Unary system
---------------

public export
UnarySystem : {a : Type} -> {b : Type} -> Set a -> Set b -> Type
UnarySystem dom cod = (SetDec dom, SetDec cod, UnaryFn dom cod)

-- export
-- unarySystem : {s : Set a} -> SetDec s -> (x : a) -> Elem x s -> UnarySystem s
-- unarySystem sd x prf = (sd, (x ** prf))

-- public export
-- setDec : {s : Set a} -> UnarySystem s -> SetDec s
-- setDec (s,_) = s
