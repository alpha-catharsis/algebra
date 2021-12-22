---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Fn.Fn

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

----------------------
-- Function definition
----------------------

public export
Fn : Set a -> Set b -> Type
Fn d c = ProvenElem d -> ProvenElem c

public export
0 dom : {d : Set a} -> {c : Set b} -> Fn d c -> Set a
dom _ = d

public export
0 cod : {d : Set a} -> {c : Set b} -> Fn d c -> Set b
cod _ = c
