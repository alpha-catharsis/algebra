module Data.Algebra.Semigroup

import Data.Algebra.Magma
import Data.Algebra.Set

public export
data Semigroup : Type where
  MkSemigroup : (s : Magma) ->
                {auto prf : (x : setType s) -> (y : setType s) ->
                (z : setType s) -> binop s (binop s x y) z =
                (binop s x (binop s y z))} -> Semigroup

public export
set : Semigroup -> Set
set (MkSemigroup s) = set s

public export
setType : Semigroup -> Type
setType = setType . set

public export
setOp : (s : Semigroup) -> (setType s -> setType s -> setType s)
setOp (MkSemigroup s) = setOp s

public export
binop : (s : Semigroup) -> setType s -> setType s -> setType s
binop (MkSemigroup s) x y = binop s x y
