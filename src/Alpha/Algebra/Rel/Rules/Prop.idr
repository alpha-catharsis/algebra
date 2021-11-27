---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.Rules.Prop

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Set.Set

---------------------
-- Reflexive relation
---------------------

public export
0 RelRefl : RelPty (a,a) -> Type
RelRefl pty = {x : a} -> pty (x,x)

-----------------------
-- Irreflexive relation
-----------------------

public export
0 RelIrrefl : RelPty (a,a) -> Type
RelIrrefl pty = {x : a} -> Not (pty (x,x))

---------------------
-- Symmetric relation
---------------------

public export
0 RelSymm : RelPty (a,a) -> Type
RelSymm pty = {x : a} -> {y : a} -> pty (x,y) -> pty (y,x)

-------------------------
-- Antisymmetric relation
-------------------------

public export
0 RelAntiSymm : RelPty (a,a) -> RelPty (a,a) -> Type
RelAntiSymm pty eqpty = {x : a} -> {y : a} -> pty (x,y) -> pty (y,x) ->
                        eqpty (x,y)

---------------------
-- Asymmetric relation
---------------------

public export
0 RelAsymm : RelPty (a,a) -> Type
RelAsymm pty = {x : a} -> {y : a} -> pty (x,y) -> Not (pty (y,x))

----------------------
-- Transitive relation
----------------------

public export
0 RelTrans : RelPty (a,a) -> Type
RelTrans pty = {x : a} -> {y : a} -> {z : a} -> pty (x,y) -> pty (y,z) ->
               pty (x,z)
