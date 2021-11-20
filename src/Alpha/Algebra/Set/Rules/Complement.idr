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
0 complRule : (SetPrf s x -> Void) -> SetPrf (compl s) x
complRule = id

public export
0 complNotRule : SetPrf s x -> SetPrf (compl s) x -> Void
complNotRule prf = \f => f prf

public export
0 invComplRule : (SetPrf (compl s) x -> Void) -> SetPrf s x
invComplRule prf = void (prf f)
  where f : SetPrf s x -> Void
        f prf' = f prf'

public export
0 invComplNotRule : SetPrf (compl s) x -> SetPrf s x -> Void
invComplNotRule = id

--------------------------
-- Double complement rules
--------------------------

public export
0 dblComplRule : SetPrf s x -> SetPrf (compl (compl s)) x
dblComplRule prf = \f => f prf

public export
0 dblComplNotRule : (SetPrf s x -> Void) ->
                    SetPrf (compl (compl s)) x -> Void
dblComplNotRule contra = \f => f contra

public export
0 invDblComplRule : SetPrf (compl (compl s)) x -> SetPrf s x
invDblComplRule prf = void (prf f)
  where f : SetPrf s x -> Void
        f prf' = f prf'

public export
0 invDblComplNotRule : (SetPrf (compl (compl s)) x -> Void) ->
                       SetPrf s x -> Void
invDblComplNotRule contra = \y => contra (\f => contra
                               (\g => contra (\f1 => contra (\g1 => f y))))
