---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Prod

-------------------
-- External imports
-------------------

import Data.DPair
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
0 ProdPrfTy : SetPrfTy a -> SetPrfTy b -> SetPrfTy (a,b)
ProdPrfTy lpf rpf (x,y) = (lpf x, rpf y)

public export
prod : Set lpty -> Set rpty -> Set (ProdPrfTy lpty rpty)
prod ls rs (x,y) = decAnd (ls x) (rs y)

----------------
-- Set coproduct
----------------

public export
0 CoprodPrfTy : SetPrfTy a -> SetPrfTy b -> SetPrfTy (Either a b)
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
pointedProd (MkPointed ls (Element x lprf)) (MkPointed rs (Element y rprf)) =
        MkPointed (prod ls rs) (Element (x,y) (lprf, rprf))
