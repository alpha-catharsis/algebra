---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Rel

-------------------
-- External imports
-------------------

import Decidable.Decidable

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

-----------------
-- Rel definition
-----------------

public export
Rel : Type -> Type -> Type
Rel a b = Set (a,b)

public export
relPrf : Rel a b -> (p : (a,b)) -> Type
relPrf = setPrf

public export
relDec : (r : Rel a b) -> (p : (a,b)) -> Dec (relPrf r p)
relDec = setDec

public export
areRelated : (x : a) -> (y : b) -> (r : Rel a b) -> Dec (relPrf r (x,y))
areRelated x y r = relDec r (x,y)

public export
related : (x : a) -> (y : b) -> (r : Rel a b) -> Bool
related x y r = isYes (areRelated x y r)
