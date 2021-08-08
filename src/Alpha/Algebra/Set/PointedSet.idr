---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.PointedSet

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Function.NullryFn
import Alpha.Algebra.Set.Set

--------------
-- Pointed set
--------------

public export
PointedSet : {a : Type} -> Set a -> Type
PointedSet s = (SetDec s, NullryFn s)

export
pointedSet : {s : Set a} -> SetDec s -> NullryFn s -> PointedSet s
pointedSet sd f = (sd, f)

-- export
-- pointedSet : {s : Set a} -> SetDec s -> (x : a) -> Elem x s -> PointedSet s
-- pointedSet sd x prf = (sd, (x ** prf))

public export
setDec : {s : Set a} -> PointedSet s -> SetDec s
setDec (s,_) = s

public export
basepoint : {s : Set a} -> PointedSet s -> a
basepoint (_,(x ** _)) = x

public export
basepointPrf : {s : Set a} -> (ps : PointedSet s) ->
               Elem (basepoint ps) s
basepointPrf (_,(_ ** prf)) = prf
