---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.DerivedOps

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.BasicOps
import Alpha.Decidable

-----------------
-- Set difference
-----------------

public export
Difference : (t : Type) -> (u : Type) -> (a : Type) ->
             (Set t a, Set u a) => Type
Difference t u a = Intersection t (Complement u a) a

public export
difference : (Set t a, Set u a) => t -> u -> Difference t u a
difference ls rs = MkIntersection ls (MkComplement rs)

public export
differenceLeftSet : (Set t a, Set u a) => Difference t u a -> t
differenceLeftSet = intersectionLeftSet

public export
differenceRightSet : (Set t a, Set u a) => Difference t u a -> u
differenceRightSet = complementSet . intersectionRightSet

---------------------------
-- Set symmetric difference
---------------------------

public export
SymDifference : (t : Type) -> (u : Type) -> (a : Type) ->
                (Set t a, Set u a) => Type
SymDifference t u a = Union (Difference t u a) (Difference u t a) a

public export
symDifference : (Set t a, Set u a) => t -> u -> SymDifference t u a
symDifference ls rs = MkUnion (difference ls rs) (difference rs ls)

public export
symDifferenceLeftSet : (Set t a, Set u a) => SymDifference t u a -> t
symDifferenceLeftSet = differenceLeftSet . unionLeftSet

public export
symDifferenceRightSet : (Set t a, Set u a) => SymDifference t u a -> u
symDifferenceRightSet = differenceLeftSet . unionRightSet
