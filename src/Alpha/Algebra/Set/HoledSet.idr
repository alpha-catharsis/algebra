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
HoledSetFpt : (v : a) -> SetFpt a
HoledSetFpt v x = (x = v) -> Void

public export
holedSet : DecEq a => (v : a) -> Set (HoledSetFpt v)
holedSet v x = decNot (decEq x v)
