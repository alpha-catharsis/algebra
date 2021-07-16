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

import Alpha.Algebra.Set.Set

------------------
-- Proposition set
------------------

export
propSet : (f : a -> Bool) -> Set (\x => f x = True) a
propSet f = MkSet (\x => decEq (f x) True)

export
elemPropSet : {x : a} -> {f : a -> Bool} -> {auto prf : f x = True} ->
              Elem x (propSet f)
elemPropSet = MkElem _ _ prf

export
notElemPropSet : {x : a} -> {f : a -> Bool} ->
                 {auto contra : (f x = True) -> Void} ->
                 Elem x (propSet f) -> Void
notElemPropSet (MkElem _ _ prf) = contra prf
