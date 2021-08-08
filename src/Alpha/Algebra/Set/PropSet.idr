---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.PropSet

-------------------
-- External imports
-------------------

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Function.NullryFn
import Alpha.Algebra.Set.PointedSet
import Alpha.Algebra.Set.Set

------------------
-- Proposition set
------------------

public export
PropSet : (a -> Bool) -> Set a
PropSet f x = (f x = True)

public export
propSet : (f : a -> Bool) -> SetDec (PropSet f)
propSet f x = decEq (f x) True

export
propPointedSet : {f : (a -> Bool)} -> SetDec (PropSet f) -> (x : a) ->
                 {auto prf : f x = True} -> PointedSet (PropSet f)
propPointedSet sd x = pointedSet sd x prf
