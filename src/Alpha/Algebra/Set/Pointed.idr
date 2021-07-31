---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Pointed

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.ProductOps

--------------------
-- Pointed interface
--------------------

public export
interface Set t a => Pointed t a where
  basepoint : t -> a
  basepointPrf : (s : t) -> SetElemPrf (basepoint s) s

export
(Pointed t a, Pointed u b) => Pointed (Product t u) (a,b) where
  basepoint (MkProduct ls rs) = (basepoint ls, basepoint rs)
  basepointPrf (MkProduct ls rs) = MkElemProduct (basepoint ls, basepoint rs)
                                   ls rs (basepointPrf ls, basepointPrf rs)
