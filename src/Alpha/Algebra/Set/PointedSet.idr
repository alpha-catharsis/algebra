---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.PointedSet

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Function
import Alpha.Algebra.Set.Set

--------------
-- Pointed set
--------------

public export
PointedSet : {a : Type} -> {fpt : SetFpt a} -> Set fpt -> Type
PointedSet _ = NullryFn fpt

public export
pointedSet : (s : Set fpt) -> (x : a) -> (prf : Elem x fpt) -> PointedSet s
pointedSet _ x prf = (x ** prf)

public export
basepoint : {fpt : SetFpt a} -> {s : Set fpt} -> PointedSet s -> a
basepoint (x ** _) = x

