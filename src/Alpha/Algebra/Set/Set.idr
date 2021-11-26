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
0 SetPty : Type -> Type
SetPty a = (x : a) -> Type

public export
0 Set : SetPty a -> Type
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
0 ProvenElem : {a : Type} -> SetPty a -> Type
ProvenElem pty = Subset a pty

public export
0 DisprovenElem : {a : Type} -> SetPty a -> Type
DisprovenElem pty = ProvenElem (Not . pty)

public export
0 EitherElem : {a : Type} -> SetPty a -> Type
EitherElem pty = Either (DisprovenElem pty) (ProvenElem pty)

public export
provenElem : {0 pty : SetPty a} -> ProvenElem pty -> a
provenElem = fst

public export
0 provenElemPrf : (pe : ProvenElem pty) -> pty (provenElem pe)
provenElemPrf = snd

public export
projectElem : {0 pty : SetPty a} -> {0 pty' : SetPty a} ->
              (0 f : {x : a} -> pty x -> pty' x) ->
              ProvenElem pty -> ProvenElem pty'
projectElem f pe = Element (provenElem pe) (f (provenElemPrf pe))

------------------
-- Element proving
------------------

public export
eitherElem : (x : a) -> {0 pty : SetPty a} -> (s : Set pty) -> EitherElem pty
eitherElem x s = case isElem x s of
  No contra => Left (Element x contra)
  Yes prf => Right (Element x prf)
