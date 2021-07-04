module Alpha.Algebra.UnarySystem

import Alpha.Algebra.Op
import Alpha.Algebra.Set

public export
data UnarySystem : Type -> Type where
  MkUnarySystem : (s : Set t) -> (f : UnOp t) ->
                  {auto prf : ClosedUnOp f s} ->
                  UnarySystem t

public export
set : UnarySystem t -> Set t
set (MkUnarySystem s _) = s

public export
unop : (s : UnarySystem t) -> UnOp t
unop (MkUnarySystem _ f) = f
