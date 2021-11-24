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
import Alpha.Algebra.Set.Set
import Alpha.Decidable

--------------
-- Set product
--------------

public export
ProdPty : SetPty a -> SetPty b -> SetPty (a,b)
ProdPty lpty rpty (x,y) = (lpty x, rpty y)

public export
prod : Set lpty -> Set rpty -> Set (ProdPty lpty rpty)
prod ls rs (x,y) = decAnd (ls x) (rs y)

public export
prodProvenElem : ProvenElem lpty -> ProvenElem rpty ->
                 ProvenElem (ProdPty lpty rpty)
prodProvenElem px py = Element (provenElem px, provenElem py)
                               (provenElemPrf px, provenElemPrf py)

----------------
-- Set coproduct
----------------

public export
CoprodPty : SetPty a -> SetPty b -> SetPty (Either a b)
CoprodPty lpty rpty e = case e of
                             Left x => lpty x
                             Right y => rpty y

coprod : Set lpty -> Set rpty -> Set (CoprodPty lpty rpty)
coprod ls rs e = case e of
                      Left x => ls x
                      Right y => rs y


----------------------
-- Set pointed product
----------------------

public export
pointedProd : Pointed lpty -> Pointed rpty -> Pointed (ProdPty lpty rpty)
pointedProd lp rp = makePointed (prod (pointedSet lp) (pointedSet rp))
                    (Element (basepoint lp, basepoint rp)
                             (basepointPrf lp, basepointPrf rp))
