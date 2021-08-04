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
ProductPrf : SetFpt a -> SetFpt b -> SetFpt (a,b)
ProductPrf lfpt rfpt (a,b) = (lfpt a,rfpt b)

public export
product : SetFn lfpt -> SetFn rfpt -> SetFn (ProductPrf lfpt rfpt)
product lf rf (x,y) = decAnd (lf x) (rf y)

export
elemProduct : SetPrf lfpt a -> SetPrf rfpt b ->
              SetPrf (ProductPrf lfpt rfpt) (a,b)
elemProduct lprf rprf = (lprf,rprf)

export
notElemProductLeft : SetContra lfpt a -> SetContra (ProductPrf lfpt _) (a,b)
notElemProductLeft lcontra = lcontra . fst

export
notElemProductRight : SetContra rfpt b -> SetContra (ProductPrf _ rfpt) (a,b)
notElemProductRight rcontra = rcontra . snd

----------------
-- Set coproduct
----------------

public export
CoproductPrf : SetFpt a -> SetFpt b -> SetFpt (Either a b)
CoproductPrf lfpt rfpt = either lfpt rfpt

public export
coproduct : SetFn lfpt -> SetFn rfpt -> SetFn (CoproductPrf lfpt rfpt)
coproduct lf rf e = case e of
  Left x => lf x
  Right y => rf y

export
elemCoproductLeft : SetPrf lfpt x -> SetPrf (CoproductPrf lfpt rfpt) (Left x)
elemCoproductLeft = id

export
elemCoproductRight : SetPrf rfpt x -> SetPrf (CoproductPrf lfpt rfpt) (Right x)
elemCoproductRight = id

export
notElemCoproductLeft : SetContra lfpt x ->
                       SetContra (CoproductPrf lfpt rfpt) (Left x)
notElemCoproductLeft = id

export
notElemCoproductRight : SetContra rfpt x ->
                        SetContra (CoproductPrf lfpt rfpt) (Right x)
notElemCoproductRight = id
