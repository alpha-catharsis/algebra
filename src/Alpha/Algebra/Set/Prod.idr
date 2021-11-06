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
prod s s' = (\(x,y) => (fst s x, fst s' y) **
             \(x,y) => decAnd (snd s x) (snd s' y))

----------------
-- Set coproduct
----------------

public export
coprod : Set a -> Set b -> Set (Either a b)
coprod s s' = ((\e => case e of
                   Left lx => fst s lx
                   Right rx => fst s' rx) **
               (\e => case e of
                   Left lx => snd s lx
                   Right rx => snd s' rx))

----------------------
-- Set pointed product
----------------------

public export
pointedProd : DecEq a => Pointed a -> Pointed b -> Pointed (a,b)
pointedProd (s ** (x ** prf)) (s' ** (y ** prf')) =
               (prod s s' ** ((x,y) ** (prf, prf')))
