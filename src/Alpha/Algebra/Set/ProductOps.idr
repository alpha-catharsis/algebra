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
product : Set lfpt a -> Set rfpt b -> Set (\x => (lfpt (Builtin.fst x), rfpt (Builtin.snd x))) (a, b)
product (MkSet lf) (MkSet rf) = MkSet (\x => decAnd (lf (fst x)) (rf (snd x)))

public export
elemProduct : {ls : Set lfpt a} -> {rs : Set rfpt b} -> Elem x ls -> Elem y rs -> Elem (x, y) (product ls rs)
elemProduct (MkElem _ _ lprf) (MkElem _ _ rprf) = MkElem _ _ (lprf, rprf)


public export
notElemProductLeft : {x : a} -> {y : b} -> {0 lfpt : a -> Type} -> {0 rfpt : a -> Type} -> {ls : Set lfpt a} -> {rs : Set rfpt b} ->
                     (Elem x ls -> Void) -> Elem (x, y) (product ls rs) -> Void
notElemProductLeft lcontra = \(MkElem _ _ pprf) => lcontra (MkElem _ _ (fst pprf))

public export
notElemProductRight : {x : a} -> {y : b} -> {0 lfpt : a -> Type} -> {0 rfpt : a -> Type} -> {ls : Set lfpt a} -> {rs : Set rfpt b} ->
                      (Elem y rs -> Void) -> Elem (x, y) (product ls rs) -> Void
notElemProductRight rcontra = \(MkElem _ _ pprf) => rcontra (MkElem _ _ (snd pprf))

----------------
-- Set coproduct
----------------

public export
coproduct : Set lfpt a -> Set rfpt b -> Set (\ex => either lfpt rfpt ex) (Either a b)
coproduct (MkSet lf) (MkSet rf) = MkSet (\ex => case ex of
  Left lx => lf lx
  Right rx => rf rx)

public export
elemCoproductLeft : {x : a} -> {y : b} -> {0 lfpt : a -> Type} -> {0 rfpt : b -> Type} -> {ls : Set lfpt a} -> {rs : Set rfpt b} ->
                    Elem x ls -> Elem (Left x) (coproduct ls rs)
elemCoproductLeft (MkElem _ _ lprf) = MkElem _ _ lprf

public export
elemCoproductRight : {x : a} -> {y : b} -> {0 lfpt : a -> Type} -> {0 rfpt : b -> Type} -> {ls : Set lfpt a} -> {rs : Set rfpt b} ->
                     Elem y rs -> Elem (Right y) (coproduct ls rs)
elemCoproductRight (MkElem _ _ rprf) = MkElem _ _ rprf
