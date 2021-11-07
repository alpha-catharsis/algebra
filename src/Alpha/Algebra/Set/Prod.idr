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
prod : Set a -> Set b -> Set (a,b)
prod ls rs = (\(x,y) => (setPrf ls x, setPrf rs y) **
              \(x,y) => decAnd (setDec ls x) (setDec rs y))

----------------
-- Set coproduct
----------------

public export
coprod : Set a -> Set b -> Set (Either a b)
coprod ls rs = ((\e => case e of
                   Left lx => setPrf ls lx
                   Right rx => setPrf rs rx) **
               (\e => case e of
                   Left lx => setDec ls lx
                   Right rx => setDec rs rx))

----------------------
-- Set pointed product
----------------------

public export
pointedProd : DecEq a => Pointed a -> Pointed b -> Pointed (a,b)
pointedProd (ls ** (x ** lprf)) (rs ** (y ** rprf)) =
               (prod ls rs ** ((x,y) ** (lprf, rprf)))
