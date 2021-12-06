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
interface Rel t a a => RelRefl t a | t where
  0 relRefl : (r : t) -> {x : a} -> RelPrf r (x,x)

-----------------------
-- Irreflexive relation
-----------------------

public export
interface Rel t a a => RelIrrefl t a | t where
  0 relIrrefl : (r : t) -> {x : a} -> Not (RelPrf r (x,x))

---------------------
-- Symmetric relation
---------------------

public export
interface Rel t a a => RelSymm t a | t where
  0 relSymm : (r : t) -> {x : a} -> {y : a} -> RelPrf r (x,y) -> RelPrf r (y,x)

-------------------------
-- Antisymmetric relation
-------------------------

public export
interface Rel t a a => RelAntiSymm t a | t where
  0 relAntiSymmEq : (r : t) -> RelPrfTy a a
  0 relAntiSymm : (r : t) -> {x : a} -> {y : a} -> RelPrf r (x,y) ->
                  RelPrf r (y,x) -> relAntiSymmEq r (x,y)

---------------------
-- Asymmetric relation
---------------------

public export
interface Rel t a a => RelAsymm t a | t where
  0 relAsymm : (r : t) -> {x : a} -> {y : a} -> RelPrf r (x,y) ->
               Not (RelPrf r (y,x))

----------------------
-- Transitive relation
----------------------

public export
interface Rel t a a => RelTrans t a | t where
  0 relTrans : (r : t) -> {x : a} -> {y : a} -> {z : a} -> RelPrf r (x,y) ->
               RelPrf r (y,z) -> RelPrf r (x,z)
