---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Set

-------------------
-- External imports
-------------------

import Data.Bool
import Decidable.Decidable

----------------
-- Set interface
----------------

public export
interface Set t a | t where
  SetElemPrf : (x : a) -> (s : t) -> Type
  isElem : (x : a) -> (s : t) -> Dec (SetElemPrf x s)

export
elem : Set t a => (x : a) -> (s : t) -> Bool
elem x s = isYes (isElem x s)

export
notElem : Set t a => (x : a) -> (s : t) -> Bool
notElem x s = not (elem x s)
