---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Ops

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
import Alpha.Decidable

-------------
-- Complement
-------------

public export
data Compl : Type -> Type -> Type where
  MkCompl : Set t a => t -> Compl t a

public export
compl : Set t a => t -> Compl t a
compl = MkCompl

public export
complSet : Compl t a -> t
complSet (MkCompl s) = s

public export
0 ComplPrf : Set t a => t -> SetPrfTy a
ComplPrf s = Not . SetPrf s

public export
Set t a => Set (Compl t a) a where
  SetPrf cs = ComplPrf (complSet cs)

public export
DecSet t a => DecSet (Compl t a) a where
  isElem x (MkCompl s) = decNot (isElem x s)

---------------
-- Intersection
---------------

public export
data Inter : Type -> Type -> Type -> Type where
  MkInter : Set lt a => Set rt a => lt -> rt -> Inter lt rt a

public export
inter : Set lt a => Set rt a => lt -> rt -> Inter lt rt a
inter = MkInter

public export
interLeftSet : Inter lt rt a -> lt
interLeftSet (MkInter ls _) = ls

public export
interRightSet : Inter lt rt a -> rt
interRightSet (MkInter _ rs) = rs

public export
0 InterPrf : Set lt a => Set rt a => lt -> rt -> SetPrfTy a
InterPrf ls rs x = (SetPrf ls x, SetPrf rs x)

public export
Set lt a => Set rt a => Set (Inter lt rt a) a where
  SetPrf is = InterPrf (interLeftSet is) (interRightSet is)

public export
DecSet lt a => DecSet rt a => DecSet (Inter lt rt a) a where
  isElem x (MkInter ls rs) = decAnd (isElem x ls) (isElem x rs)

--------
-- Union
--------

public export
data Union : Type -> Type -> Type -> Type where
  MkUnion : Set lt a => Set rt a => lt -> rt -> Union lt rt a

public export
union : Set lt a => Set rt a => lt -> rt -> Union lt rt a
union = MkUnion

public export
unionLeftSet : Union lt rt a -> lt
unionLeftSet (MkUnion ls _) = ls

public export
unionRightSet : Union lt rt a -> rt
unionRightSet (MkUnion _ rs) = rs

public export
0 UnionPrf : Set lt a => Set rt a => lt -> rt -> SetPrfTy a
UnionPrf ls rs x = Either (SetPrf ls x) (SetPrf rs x)

public export
Set lt a => Set rt a => Set (Union lt rt a) a where
  SetPrf us = UnionPrf (unionLeftSet us) (unionRightSet us)

public export
DecSet lt a => DecSet rt a => DecSet (Union lt rt a) a where
  isElem x (MkUnion ls rs) = decOr (isElem x ls) (isElem x rs)

-------------
-- Difference
-------------

public export
Diff : Type -> Type -> Type -> Type
Diff lt rt a = Inter lt (Compl rt a) a

public export
diff : Set lt a => Set rt a => lt -> rt -> Diff lt rt a
diff ls rs = inter ls (compl rs)

public export
0 DiffPrf : Set lt a => Set rt a => lt -> rt -> SetPrfTy a
DiffPrf ls rs = InterPrf ls (compl rs)

-----------------------
-- Symmetric difference
-----------------------

public export
SymmDiff : Type -> Type -> Type -> Type
SymmDiff lt rt a = Union (Diff lt rt a) (Diff rt lt a) a

public export
symmDiff : Set lt a => Set rt a => lt -> rt -> SymmDiff lt rt a
symmDiff ls rs = union (diff ls rs) (diff rs ls)

public export
0 SymmDiffPrf : Set lt a => Set rt a => lt -> rt -> SetPrfTy a
SymmDiffPrf ls rs = UnionPrf (diff ls rs) (diff rs ls)
