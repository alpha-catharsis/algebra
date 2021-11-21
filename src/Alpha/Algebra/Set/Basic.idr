---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Basic

-------------------
-- External imports
-------------------

import Data.DPair

-------------------
-- Internal imports
-------------------

import public Alpha.Algebra.Set.Ops
import public Alpha.Algebra.Set.Set

---------------
-- Universe set
---------------

public export
univ : Set a
univ = MkSet (const ()) (const (Yes ()))

public export
univProvenElem : a -> ProvenElem (univ {a})
univProvenElem x = MkProvenElem x ()

------------
-- Empty set
------------

public export
empty : Set a
empty = compl univ

Uninhabited (SetPrf Basic.empty x) where
  uninhabited f = f ()

public export
emptyDisproven : a -> DisprovenElem (empty {a})
emptyDisproven x = MkDisprovenElem x absurd

--------------
-- Set of sets
--------------

public export
sets : Set (Set a)
sets = univ

----------
-- Nat set
----------

public export
nats : Set Nat
nats = univ

public export
provenNat : Nat -> ProvenElem {a=Nat} Basic.nats
provenNat n = univProvenElem n
