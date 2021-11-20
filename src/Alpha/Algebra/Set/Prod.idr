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
prod : Set a -> Set b -> Set (a,b)
prod ls rs = MkSet (\(x,y) => (SetPrf ls x, SetPrf rs y))
             (\(x,y) => decAnd (setDec ls x) (setDec rs y))

----------------
-- Set coproduct
----------------

public export
coprod : Set a -> Set b -> Set (Either a b)
coprod ls rs = MkSet (\e => case e of
                              Left x => SetPrf ls x
                              Right y => SetPrf rs y)
                     (\e => case e of
                              Left x => setDec ls x
                              Right y => setDec rs y)

----------------------
-- Set pointed product
----------------------

public export
pointedProd : Pointed a -> Pointed b -> Pointed (a,b)
pointedProd lp rp = MkPointed (prod (pointedSet lp)  (pointedSet rp))
                    (MkProvenElem (basepoint lp, basepoint rp)
                                  (basepointPrf lp, basepointPrf rp))
