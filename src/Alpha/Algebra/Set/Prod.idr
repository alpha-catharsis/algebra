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
Prod : Set a -> Set b -> Set (a,b)
Prod ls rs (x,y) = (ls x, rs y)

public export
prod : DecSet ls -> DecSet rs -> DecSet (Prod ls rs)
prod ls rs (x,y) = decAnd (isElem x ls) (isElem y rs)

----------------
-- Set coproduct
----------------

public export
Coprod : Set a -> Set b -> Set (Either a b)
Coprod ls rs e = case e of
  Left x => ls x
  Right y => rs y

public export
coprod : DecSet ls -> DecSet rs -> DecSet (Coprod ls rs)
coprod ls rs e = case e of
  Left x => isElem x ls
  Right y => isElem y rs

----------------------
-- Pointed set product
----------------------

public export
pointedProd : Pointed ls -> Pointed rs -> Pointed (Prod ls rs)
pointedProd (MkPointed ls x lprf) (MkPointed rs y rprf) = MkPointed (Prod ls rs) (x,y) (lprf, rprf)

public export
decPointedProd : DecPointed ls -> DecPointed rs -> DecPointed (Prod ls rs)
decPointedProd (MkDecPointed lpnt lds) (MkDecPointed rpnt rds) = MkDecPointed (pointedProd lpnt rpnt) (prod lds rds)

------------------
-- Element Product
------------------

public export
prodProvenElem : ProvenElem ls -> ProvenElem rs -> ProvenElem (Prod ls rs)
prodProvenElem lpe rpe = MkProvenElem (provenElem lpe, provenElem rpe) (elemPrf lpe, elemPrf rpe)

--------------------
-- Element Coproduct
--------------------

public export
coprodLeftElem : ProvenElem ls -> ProvenElem (Coprod ls rs)
coprodLeftElem pe = MkProvenElem (Left (provenElem pe)) (elemPrf pe)

public export
coprodRightElem : ProvenElem rs -> ProvenElem (Coprod ls rs)
coprodRightElem pe = MkProvenElem (Right (provenElem pe)) (elemPrf pe)
