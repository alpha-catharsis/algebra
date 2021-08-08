---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.UnarySystem

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Function.NullryFn
import Alpha.Algebra.Function.UnaryFn
import Alpha.Algebra.Set.Set

---------------
-- Unary system
---------------

public export
UnarySystem : {a : Type} -> Set a -> Type
UnarySystem s = (SetDec s, UnaryFn s s)

export
unarySystem : {s : Set a} -> SetDec s -> UnaryFn s s -> UnarySystem s
unarySystem sd f = (sd, f)

public export
setDec : {s : Set a} -> UnarySystem s -> SetDec s
setDec (sd,_) = sd

public export
project : {a : Type} -> {s : Set a} -> UnarySystem s -> NullryFn s ->
          NullryFn s
project (_,f) x = f x

public export
apply : {a : Type} -> {s : Set a} -> UnarySystem s -> NullryFn s -> a
apply (_,f) x = let (y ** _) = f x in y
