---------------------
 -- Module declaration
---------------------

module Alpha.Algebra.Set.ListSet

-------------------
-- External imports
-------------------

import Data.List.Elem as LE

import Decidable.Equality

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Function.NullryFn
import Alpha.Algebra.Set.PointedSet
import Alpha.Algebra.Set.Set

-----------
-- List set
-----------

public export
ListSet : List a -> Set a
ListSet xs x = LE.Elem x xs

public export
listSet : DecEq a => (xs : List a) -> SetDec (ListSet xs)
listSet xs x = LE.isElem x xs

export
listPointedSet : {xs : List a} -> SetDec (ListSet xs) -> (x : a) ->
                 {auto prf : LE.Elem x xs} -> PointedSet (ListSet xs)
listPointedSet sd x = pointedSet sd x prf
