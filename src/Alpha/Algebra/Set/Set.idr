---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Set

-------------------
-- External imports
-------------------

import Data.DPair
import Decidable.Decidable

-----------------
-- Set definition
-----------------

public export
0 SetPrf : Type -> Type
SetPrf a = (x : a) -> Type

public export
0 SetContra : Type -> Type
SetContra a = Not (SetPrf a)

public export
0 Set : SetPrf a -> Type
Set pty = (x : a) -> Dec (pty x)

public export
isElem : (x : a) -> Set pty -> Dec (pty x)
isElem x s = s x

public export
elem : (x : a) -> Set {a} pty -> Bool
elem x s = isYes (isElem x s)

-----------------
-- Proven element
-----------------

public export
0 ProvenElem : {a : Type} -> SetPrf a -> Type
ProvenElem pty = Subset a pty

public export
provenElem : {0 pty : SetPrf a} -> ProvenElem pty -> a
provenElem = fst

public export
0 provenElemPrf : (pe : ProvenElem pty) -> pty (provenElem pe)
provenElemPrf = snd

--------------------
-- Disproven element
--------------------

public export
0 DisprovenElem : {a : Type} -> SetPrf a -> Type
DisprovenElem pty = ProvenElem (Not . pty)

public export
disprovenElem : {0 pty : SetPrf a} -> DisprovenElem pty -> a
disprovenElem = fst

public export
0 disprovenElemPrf : (pe : DisprovenElem pty) -> Not (pty (disprovenElem pe))
disprovenElemPrf = snd

------------------
-- Element proving
------------------

public export
eitherProvenPrf : (x : a) -> (s : Set pty) -> Either (Not (pty x)) (pty x)
eitherProvenPrf x s = case isElem x s of
    No contra => Left contra
    Yes prf => Right prf

public export
eitherProvenElem : (x : a) -> {0 pty : SetPrf a} -> (s : Set pty) ->
                   Either (DisprovenElem pty) (ProvenElem pty)
eitherProvenElem x s = case isElem x s of
  No contra => Left (Element x contra)
  Yes prf => Right (Element x prf)
