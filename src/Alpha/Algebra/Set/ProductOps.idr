---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.ProductOps

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.BasicOps
import Alpha.Algebra.Set.DerivedOps
import Alpha.Algebra.Set.Set
import Alpha.Decidable

--------------
-- Set product
--------------

public export
product : Set a -> Set b -> Set (a, b)
product ls rs = MkSet (\x => (setFpt ls (fst x), setFpt rs (snd x)))
                (\x => decAnd (setDec ls (fst x)) (setDec rs (snd x)))

export
elemProduct : {ls : Set a} -> {rs : Set b} -> Elem x ls ->
              Elem y rs -> Elem (x, y) (product ls rs)
elemProduct (MkElem _ _ lprf) (MkElem _ _ rprf) = MkElem _ _ (lprf, rprf)

export
notElemProductLeft : {x : a} -> {y : b} -> {ls : Set a} -> {rs : Set b} ->
                     (Elem x ls -> Void) -> Elem (x, y) (product ls rs) -> Void
notElemProductLeft lcontra = \(MkElem _ _ pprf) => lcontra (MkElem _ _ (fst pprf))

export
notElemProductRight : {x : a} -> {y : b} -> {ls : Set a} -> {rs : Set b} ->
                      (Elem y rs -> Void) -> Elem (x, y) (product ls rs) ->
                      Void
notElemProductRight rcontra = \(MkElem _ _ pprf) => rcontra (MkElem _ _ (snd pprf))

----------------
-- Set coproduct
----------------

public export
coproduct : Set a -> Set b -> Set (Either a b)
coproduct ls rs = MkSet (\ex => either (setFpt ls) (setFpt rs) ex)
                  (\ex => case ex of
                            Left lx => setDec ls lx
                            Right rx => setDec rs rx)

export
elemCoproductLeft : {x : a} -> {y : b} -> {ls : Set a} -> {rs : Set b} ->
                    Elem x ls -> Elem (Left x) (coproduct ls rs)
elemCoproductLeft (MkElem _ _ lprf) = MkElem _ _ lprf

export
elemCoproductRight : {x : a} -> {y : b} -> {ls : Set a} -> {rs : Set b} ->
                     Elem y rs -> Elem (Right y) (coproduct ls rs)
elemCoproductRight (MkElem _ _ rprf) = MkElem _ _ rprf
