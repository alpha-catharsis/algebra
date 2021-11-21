---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Rel.LTE

-------------------
-- External imports
-------------------

import Data.Nat

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Rel.Rel
import Alpha.Algebra.Set.Basic
import Alpha.Algebra.Set.Set

---------------
-- LTE relation
---------------

-- public export
-- lte : Rel {a=Nat} {b=Nat} Basic.nats Basic.nats
-- lte = MkRel (\pn,pm => LTE (provenElem pn) (provenElem pm))
--             (\pn,pm => isLTE (provenElem pn) (provenElem pm))

-- public export
-- lteRefl : ReflRel LTE.lte
-- lteRefl = MkReflRel (\px => LTE (provenElem px) (provenElem px))
