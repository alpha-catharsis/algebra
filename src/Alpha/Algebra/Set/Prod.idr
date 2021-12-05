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
import Alpha.Algebra.Set.Singl
import Alpha.Algebra.Set.Set
import Alpha.Decidable

--------------
-- Set product
--------------

public export
data Prod : Type -> Type -> Type -> Type where
  MkProd : Set lt a => Set rt b => lt -> rt -> Prod lt rt (a,b)

public export
prod : Set lt a => Set rt b => lt -> rt -> Prod lt rt (a,b)
prod = MkProd

public export
prodLeftSet : Prod lt rt (a,b) -> lt
prodLeftSet (MkProd ls _) = ls

public export
prodRightSet : Prod lt rt (a,b) -> rt
prodRightSet (MkProd _ rs) = rs

public export
0 ProdPrf : Set lt a => Set rt b => lt -> rt -> SetPrfTy (a,b)
ProdPrf ls rs (x,y) = (SetPrf ls x, SetPrf rs y)

public export
Set lt a => Set rt b => Set (Prod lt rt (a,b)) (a,b) where
  SetPrf ps = ProdPrf (prodLeftSet ps) (prodRightSet ps)

public export
DecSet lt a => DecSet rt b => DecSet (Prod lt rt (a,b)) (a,b) where
  isElem (x,y) (MkProd ls rs) = decAnd (isElem x ls) (isElem y rs)

----------------
-- Set coproduct
----------------

public export
data Coprod : Type -> Type -> Type -> Type where
  MkCoprod : Set lt a => Set rt b => lt -> rt -> Coprod lt rt (Either a b)

coprod : Set lt a => Set rt b => lt -> rt -> Coprod lt rt (Either a b)
coprod = MkCoprod

public export
coprodLeftSet : Coprod lt rt (Either a b) -> lt
coprodLeftSet (MkCoprod ls _) = ls

public export
coprodRightSet : Coprod lt rt (Either a b) -> rt
coprodRightSet (MkCoprod _ rs) = rs

public export
0 CoprodPrf : Set lt a => Set rt b => lt -> rt -> SetPrfTy (Either a b)
CoprodPrf ls rs e = case e of
                      Left x => SetPrf ls x
                      Right y => SetPrf rs y

public export
Set lt a => Set rt b => Set (Coprod lt rt (Either a b)) (Either a b) where
  SetPrf cs = CoprodPrf (coprodLeftSet cs) (coprodRightSet cs)

public export
DecSet lt a => DecSet rt b =>
DecSet (Coprod lt rt (Either a b)) (Either a b) where
  isElem e (MkCoprod ls rs) = case e of
                                Left x => isElem x ls
                                Right y => isElem y rs

------------------
-- Element Product
------------------

public export
prodProvenElem : Set lt a => Set rt b => {0 ls : lt} -> {0 rs : rt} ->
                 SetProvenElem ls -> SetProvenElem rs ->
                 ProvenElem (ProdPrf ls rs)
prodProvenElem lpe rpe = MkProvenElem (provenElem lpe, provenElem rpe)
                                      (elemPrf lpe, elemPrf rpe)

----------------------
-- Set pointed product
----------------------

public export
Pointed lt a => Pointed rt b => Pointed (Prod lt rt (a,b)) (a,b) where
  basepointElem (MkProd ls rs) = MkProvenElem (basepoint ls, basepoint rs)
                                              (basepointPrf ls, basepointPrf rs)
