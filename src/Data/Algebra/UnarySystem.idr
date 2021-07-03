module Data.Algebra.UnarySystem

import Data.Algebra.Set

public export
data UnarySystem : Type where
  MkUnarySystem : (s : Set) -> (f : setType s -> setType s) ->
                  {auto prf : (x : setType s) -> (SetElem s (f x))} ->
                  UnarySystem

public export
set : UnarySystem -> Set
set (MkUnarySystem s _) = s

public export
setType : UnarySystem -> Type
setType = setType . set

public export
setOp : (s : UnarySystem) -> (setType s -> setType s)
setOp (MkUnarySystem _ f) = f

public export
unop : (s : UnarySystem) -> setType s -> setType s
unop (MkUnarySystem _ f) x = f x
