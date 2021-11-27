---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Rel

-------------------
-- External imports
-------------------

import Data.DPair
import Decidable.Decidable

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

----------------------
-- Relation definition
----------------------

public export
0 RelPty : (Type, Type) -> Type
RelPty (a, b) = (a, b) -> Type

public export
0 Rel : RelPty (a, b) -> Type
Rel pty = (p : (a, b)) -> Dec (pty p)

public export
areRelated : (x : a) -> (y : b) -> {0 pty : RelPty (a,b)} -> Rel pty ->
             Dec (pty (x,y))
areRelated x y r = r (x,y)

public export
related : (x : a) -> (y : b) -> {0 pty : RelPty (a, b)} -> Rel pty -> Bool
related x y  r = isYes (areRelated x y r)

-----------------
-- Proven related
-----------------

public export
0 ProvenRelated : RelPty (a,b) -> Type
ProvenRelated pty = Subset (a, b) pty

public export
0 DisprovenRelated : RelPty (a, b) -> Type
DisprovenRelated pty = ProvenRelated (Not . pty)

public export
0 EitherRelated : RelPty (a, b) -> Type
EitherRelated pty = Either (DisprovenRelated pty) (ProvenRelated pty)

public export
provenRelated : {0 pty : RelPty (a,b)} -> ProvenRelated pty -> (a, b)
provenRelated = fst

public export
0 provenRelatedPrf : (pr : ProvenRelated pty) -> pty (provenRelated pr)
provenRelatedPrf = snd

public export
projectRelated : {0 pty : RelPty (a,b)} -> {0 pty' : RelPty (a,b)} ->
                 (0 f : {p : (a, b)} -> pty p -> pty' p) ->
                 ProvenRelated pty -> ProvenRelated pty'
projectRelated f pr = Element (provenRelated pr) (f (provenRelatedPrf pr))
