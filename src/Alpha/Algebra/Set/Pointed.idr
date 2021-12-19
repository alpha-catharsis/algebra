---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Pointed

-------------------
-- External imports
-------------------

import Data.DPair

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set

--------------
-- Pointed set
--------------

public export
data Pointed : Set a -> Type where
  MkPointed : (0 s : Set a) -> (x : a) -> (0 prf : s x) -> Pointed s

public export
data DecPointed : Set a -> Type where
  MkDecPointed : {0 s : Set a} -> (ps : Pointed s) -> (ds : DecSet s) -> DecPointed s
