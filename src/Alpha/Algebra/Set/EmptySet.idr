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
empty : Set (\x => const Void (the a x)) a
empty = MkSet (const (No id))

export
Uninhabited (Elem x EmptySet.empty) where
  uninhabited (MkElem _ _ _) impossible

export
Uninhabited (Elem x (intersection EmptySet.empty rs)) where
  uninhabited (MkElem _ _ (_, _)) impossible

export
Uninhabited (Elem x (intersection ls EmptySet.empty)) where
  uninhabited (MkElem _ _ (_, _)) impossible
