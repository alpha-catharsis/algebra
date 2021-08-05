---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.ProductOps

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Set
import Alpha.Decidable

--------------
-- Set product
--------------

public export
ProductFpt : SetFpt a -> SetFpt b -> SetFpt (a,b)
ProductFpt lfpt rfpt (x,y) = (lfpt x,rfpt y)

public export
product : Set lfpt -> Set rfpt -> Set (ProductFpt lfpt rfpt)
product lf rf (x,y) = decAnd (lf x) (rf y)

export
elemProduct : Elem x lfpt -> Elem y rfpt ->
              Elem (x,y) (ProductFpt lfpt rfpt)
elemProduct lprf rprf = (lprf,rprf)

export
notElemProductLeft : NotElem x lfpt -> NotElem (x,y) (ProductFpt lfpt _)
notElemProductLeft lcontra = lcontra . fst

export
notElemProductRight : NotElem y rfpt -> NotElem (x,y) (ProductFpt _ rfpt)
notElemProductRight rcontra = rcontra . snd

----------------
-- Set coproduct
----------------

public export
CoproductFpt : SetFpt a -> SetFpt b -> SetFpt (Either a b)
CoproductFpt lfpt rfpt = either lfpt rfpt

public export
coproduct : Set lfpt -> Set rfpt -> Set (CoproductFpt lfpt rfpt)
coproduct lf rf e = case e of
  Left x => lf x
  Right y => rf y

export
elemCoproductLeft : Elem x lfpt -> Elem (Left x) (CoproductFpt lfpt rfpt)
elemCoproductLeft = id

export
elemCoproductRight : Elem x rfpt -> Elem (Right x) (CoproductFpt lfpt rfpt)
elemCoproductRight = id

export
notElemCoproductLeft : NotElem x lfpt ->
                       NotElem (Left x) (CoproductFpt lfpt rfpt)
notElemCoproductLeft = id

export
notElemCoproductRight : NotElem x rfpt ->
                        NotElem (Right x) (CoproductFpt lfpt rfpt)
notElemCoproductRight = id
