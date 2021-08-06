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
Product : Set a -> Set b -> Set (a,b)
Product ls rs (x,y) = (ls x,rs y)

public export
product : SetDec ls -> SetDec rs -> SetDec (Product ls rs)
product lf rf (x,y) = decAnd (lf x) (rf y)

export
elemProduct : Elem x ls -> Elem y rs ->
              Elem (x,y) (Product ls rs)
elemProduct lprf rprf = (lprf,rprf)

export
notElemProductLeft : NotElem x ls -> NotElem (x,y) (Product ls _)
notElemProductLeft lcontra = lcontra . fst

export
notElemProductRight : NotElem y rs -> NotElem (x,y) (Product _ rs)
notElemProductRight rcontra = rcontra . snd

----------------
-- Set coproduct
----------------

public export
Coproduct : Set a -> Set b -> Set (Either a b)
Coproduct ls rs = either ls rs

public export
coproduct : SetDec ls -> SetDec rs -> SetDec (Coproduct ls rs)
coproduct lf rf e = case e of
  Left x => lf x
  Right y => rf y

export
elemCoproductLeft : Elem x ls -> Elem (Left x) (Coproduct ls rs)
elemCoproductLeft = id

export
elemCoproductRight : Elem x rs -> Elem (Right x) (Coproduct ls rs)
elemCoproductRight = id

export
notElemCoproductLeft : NotElem x ls ->
                       NotElem (Left x) (Coproduct ls rs)
notElemCoproductLeft = id

export
notElemCoproductRight : NotElem x rs ->
                        NotElem (Right x) (Coproduct ls rs)
notElemCoproductRight = id
