---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.DerivedOps

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.BasicOps

-----------------
-- Set difference
-----------------

public export
Difference : (t : Type) -> (u : Type) -> (Set t a, Set u a) => Type
Difference t u = Intersection t (Complement u)

public export
difference : (Set t a, Set u a) => t -> u -> Difference t u
difference ls rs = MkIntersection ls (MkComplement rs)

public export
differenceLeftSet : (Set t a, Set u a) => Difference t u -> t
differenceLeftSet = intersectionLeftSet

public export
differenceRightSet : (Set t a, Set u a) => Difference t u -> u
differenceRightSet = complementSet . intersectionRightSet

---------------------------
-- Set symmetric difference
---------------------------

public export
SymDifference : (t : Type) -> (u : Type) -> (Set t a, Set u a) => Type
SymDifference t u = Union (Difference t u) (Difference u t)

public export
symDifference : (Set t a, Set u a) => t -> u -> SymDifference t u
symDifference ls rs = MkUnion (difference ls rs) (difference rs ls)

public export
symDifferenceLeftSet : (Set t a, Set u a) => SymDifference t u -> t
symDifferenceLeftSet = differenceLeftSet . unionLeftSet

public export
symDifferenceRightSet : (Set t a, Set u a) => SymDifference t u -> u
symDifferenceRightSet = differenceLeftSet . unionRightSet
