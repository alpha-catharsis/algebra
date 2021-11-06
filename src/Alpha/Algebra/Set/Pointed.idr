---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Pointed

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

--------------
-- Pointed set
--------------

public export
Pointed : (a : Type) -> Type
Pointed a = (s : Set a ** ProvenElem s)

public export
pointedSet : {a : Type} -> (p : Pointed a) -> Set a
pointedSet p = fst p

public export
basepoint : {a : Type} -> (p : Pointed a) -> a
basepoint p = proven (snd p)
