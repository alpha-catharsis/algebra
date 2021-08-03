---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.EmptySet

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
import Alpha.Algebra.Set.BasicOps

------------
-- Empty set
------------

export
emptySet : Set a
emptySet = MkSet (const Void) (const (No id))

export
Uninhabited (Elem x EmptySet.emptySet) where
  uninhabited (MkElem _ _ _) impossible

export
Uninhabited (Elem x (intersection EmptySet.emptySet rs)) where
  uninhabited (MkElem _ _ (_, _)) impossible

export
Uninhabited (Elem x (intersection ls EmptySet.emptySet)) where
  uninhabited (MkElem _ _ (_, _)) impossible

