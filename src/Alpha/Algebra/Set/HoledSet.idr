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
HoledSet : (v : a) -> Set a
HoledSet v x = (x = v) -> Void

public export
holedSet : DecEq a => (v : a) -> SetDec (HoledSet v)
holedSet v x = decNot (decEq x v)
