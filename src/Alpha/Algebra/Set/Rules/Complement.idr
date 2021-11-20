---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Complement

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Ops
import Alpha.Algebra.Set.Set

-------------------
-- Complement rules
-------------------

public export
0 complRule : SetContra s x -> SetPrf (compl s) x
complRule = id

public export
0 complNotRule : SetPrf s x -> SetContra (compl s) x
complNotRule prf = \f => f prf

public export
0 invComplRule : SetContra (compl s) x -> SetPrf s x
invComplRule prf = void (prf f)
  where f : SetContra s x
        f prf' = f prf'

public export
0 invComplNotRule : SetPrf (compl s) x -> SetContra s x
invComplNotRule = id

--------------------------
-- Double complement rules
--------------------------

public export
0 dblComplRule : SetPrf s x -> SetPrf (compl (compl s)) x
dblComplRule prf = \f => f prf

public export
0 dblComplNotRule : SetContra s x -> SetContra (compl (compl s)) x
dblComplNotRule contra = \f => f contra

public export
0 invDblComplRule : SetPrf (compl (compl s)) x -> SetPrf s x
invDblComplRule prf = void (prf f)
  where f : SetContra s x
        f prf' = f prf'

public export
0 invDblComplNotRule : SetContra (compl (compl s)) x -> SetContra s x
invDblComplNotRule contra = \y => contra (\f => contra
                               (\g => contra (\f1 => contra (\g1 => f y))))
