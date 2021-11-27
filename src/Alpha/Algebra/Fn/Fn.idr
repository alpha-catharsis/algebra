---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Fn.Fn

-------------------
-- External imports
-------------------

import Data.DPair

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Basic
import Alpha.Algebra.Set.Set

----------------------
-- Function definition
----------------------

public export
0 Fn : SetPty a -> SetPty b -> Type
Fn dpty cpty = ProvenElem dpty -> ProvenElem cpty

public export
fn : {0 lpty : SetPty a} -> {0 rpty : SetPty b} -> Fn lpty rpty -> (x : a) ->
     {auto 0 prf : lpty x} -> b
fn f x = provenElem (f (Element x prf))

public export
ufn : Fn (UnivPty {a}) (UnivPty {a=b}) -> a -> b
ufn f x = provenElem (f (univProvenElem x))

