---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Nat

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Function.NullryFn
import Alpha.Algebra.Function.UnaryFn
import Alpha.Algebra.Set.PointedSet
import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.UnarySystem
import Alpha.Algebra.Set.UniverseSet

---------------
-- Natural sets
---------------

public export
N : Set Nat
N = UniverseSet

export
naturals : SetDec N
naturals = universeSet

public export
n0 : PointedSet N
n0 = pointedSet naturals (nullryFn N Z)

public export
n1 : PointedSet N
n1 = pointedSet naturals (nullryFn N (S Z))

public export
n0u : UnarySystem N
n0u = unarySystem naturals (\(x ** _) => (S x ** ()))
