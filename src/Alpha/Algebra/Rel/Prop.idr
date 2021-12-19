---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Prop

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Set.Set

---------------------
-- Reflexive relation
---------------------

public export
0 relRefl : Rel a a -> Type
relRefl r = {x : a} -> r (x,x)

-----------------------
-- Irreflexive relation
-----------------------

public export
0 relIrrefl : Rel a a -> Type
relIrrefl r = {x : a} -> Not (r (x,x))

---------------------
-- Symmetric relation
---------------------

public export
0 relSymm : Rel a a -> Type
relSymm r = {x : a} -> {y : a} -> r (x,y) -> r (y,x)

-------------------------
-- Antisymmetric relation
-------------------------

public export
0 relAntiSymm : Rel a a -> Rel a a -> Type
relAntiSymm r req = {x : a} -> {y : a} -> r (x,y) -> r (y,x) -> req (x,y)

---------------------
-- Asymmetric relation
---------------------

public export
0 relAsymm : Rel a a -> Type
relAsymm r = {x : a} -> {y : a} -> r (x,y) -> Not (r (y,x))

----------------------
-- Transitive relation
----------------------

public export
0 relTrans : Rel a a -> Type
relTrans r = {x : a} -> {y : a} -> {z : a} -> r (x,y) -> r (y,z) -> r (x,z)
