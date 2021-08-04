---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.HoledSet

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
import Alpha.Decidable

------------
-- Holed set
------------

public export
HoledSetPrf : (v : a) -> SetFpt a
HoledSetPrf v x = (x = v) -> Void

public export
holedSet : DecEq a => (v : a) -> SetFn (HoledSetPrf v)
holedSet v x = decNot (decEq x v)
