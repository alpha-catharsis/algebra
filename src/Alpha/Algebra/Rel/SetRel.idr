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
0 SetRel : Set (a,b) -> Rel a b
SetRel = id

public export
0 DecSetRel : {s : Set (a,b)} -> DecSet s -> DecRel (SetRel s)
DecSetRel ds p = isElem p ds
