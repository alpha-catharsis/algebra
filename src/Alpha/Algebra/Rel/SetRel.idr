---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.SetRel

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.Prod

---------------------
-- Set based relation
---------------------

public export
Set lt a => Set rt b => Rel (Prod lt rt (a,b)) a b where
  RelPrf ps = ProdPrf (prodLeftSet ps) (prodRightSet ps)

public export
DecSet lt a => DecSet rt b => DecRel (Prod lt rt (a,b)) a b where
  areRelated ps x y = isElem (x,y) ps
