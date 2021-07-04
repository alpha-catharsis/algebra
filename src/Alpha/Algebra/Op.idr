module Alpha.Algebra.Op

import Alpha.Algebra.Set

public export
UnOp : Type -> Type
UnOp t = t -> t

public export
BinOp : Type -> Type
BinOp t = t -> t -> t

public export
ClosedUnOp : {t : Type} -> (f : UnOp t) -> (s : Set t) -> Type
ClosedUnOp f s = (x : t) -> SetElem s x -> SetElem s (f x)

public export
ClosedBinOp : {t : Type} -> (f : BinOp t) -> (s : Set t) -> Type
ClosedBinOp f s = (x : t) -> (y : t) ->  SetElem s x -> SetElem s y ->
                  SetElem s (f x y)

public export
Associative : {t : Type} -> (f : BinOp t) -> Type
Associative f = (x : t) -> (y : t) -> (z : t) -> f (f x y) z = f x (f y z)
