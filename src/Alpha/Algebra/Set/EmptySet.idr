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

public export
empty : Set (\x => const Void (the a x)) a
empty = MkSet (const (No id))

public export
Uninhabited (Elem x Alpha.Algebra.Set.EmptySet.empty) where
  uninhabited (MkElem _ _ _) impossible

public export
Uninhabited (Elem x (intersection Alpha.Algebra.Set.EmptySet.empty rs)) where
  uninhabited (MkElem _ _ (_, _)) impossible

public export
Uninhabited (Elem x (intersection ls Alpha.Algebra.Set.EmptySet.empty)) where
  uninhabited (MkElem _ _ (_, _)) impossible
