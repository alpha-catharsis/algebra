---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Fn.Basic

-------------------
-- External imports
-------------------

import Data.DPair

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
import Alpha.Algebra.Fn.Fn

--------------------
-- Identity Function
--------------------

public export
fnId : Fn pty pty
fnId = id
