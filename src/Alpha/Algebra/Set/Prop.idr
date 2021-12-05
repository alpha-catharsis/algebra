---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Prop

-------------------
-- External imports
-------------------

import Data.DPair
import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

------------------
-- Proposition Set
------------------

public export
data Prop : Type -> Type where
  MkProp : (a -> Bool) -> Prop a

public export
prop : (a -> Bool) -> Prop a
prop = MkProp

public export
0 PropPrf : (a -> Bool) -> SetPrfTy a
PropPrf f x = f x = True

public export
Set (Prop a) a where
  SetPrf (MkProp f) = PropPrf f

public export
DecSet (Prop a) a where
  isElem x (MkProp f) = decEq (f x) True
