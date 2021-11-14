---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Prod

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Pointed
import Alpha.Algebra.Set.Set
import Alpha.Decidable

--------------
-- Set product
--------------

public export
ProdPrfTy : SetPrfTy a -> SetPrfTy b -> SetPrfTy (a,b)
ProdPrfTy lpf rpf (x,y) = (lpf x, rpf y)

public export
prod : Set lpty -> Set rpty -> Set (ProdPrfTy lpty rpty)
prod ls rs (x,y) = decAnd (ls x) (rs y)

----------------
-- Set coproduct
----------------

public export
CoprodPrfTy : SetPrfTy a -> SetPrfTy b -> SetPrfTy (Either a b)
CoprodPrfTy lpf rpf e =  case e of
                           Left lx => lpf lx
                           Right rx => rpf rx


public export
coprod : Set lpty -> Set rpty -> Set (CoprodPrfTy lpty rpty)
coprod ls rs e = case e of
                   Left lx => ls lx
                   Right rx => rs rx

----------------------
-- Set pointed product
----------------------

public export
pointedProd : Pointed lpty -> Pointed rpty -> Pointed (ProdPrfTy lpty rpty)
pointedProd (ls, (x ** lprf)) (rs, (y ** rprf)) = (prod ls rs,
                                                   ((x,y) ** (lprf, rprf)))
