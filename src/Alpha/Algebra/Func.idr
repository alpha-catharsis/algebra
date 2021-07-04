module Alpha.Algebra.Func

import Alpha.Algebra.Op
import Alpha.Algebra.Set

public export
UnFunc : Type -> Type -> Type
UnFunc a b = a -> b

public export
ClosedUnFunc : {a : Type} -> {b : Type} -> (f : UnFunc a b) -> (s : Set a) ->
               (s' : Set b) -> Type
ClosedUnFunc f s s' = (x : a) -> SetElem s x -> SetElem s' (f x)

public export
Morphism : {a : Type} -> {b : Type} -> (f : UnFunc a b) -> (g : BinOp a) ->
           (h : BinOp b) -> Type
Morphism f g h = (x : a) -> (y : a) -> f (g  x y) = h (f x) (f y)
