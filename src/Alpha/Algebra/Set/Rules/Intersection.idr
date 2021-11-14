---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Intersection

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Ops
import Alpha.Algebra.Set.Set

---------------------
-- Intersection rules
---------------------

public export
interRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} -> lpty x ->
            rpty x -> InterPrfTy lpty rpty x
interRule lpf rpf = (lpf, rpf)

public export
interNotLeftRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} ->
                   (lpty x -> Void) -> InterPrfTy lpty rpty x -> Void
interNotLeftRule lcontra = lcontra . fst

public export
interNotRightRule : {lpty : SetPrfTy a} -> {rpty : SetPrfTy a} ->
                    (rpty x -> Void) -> InterPrfTy lpty rpty x -> Void
interNotRightRule rcontra = rcontra . snd

public export
invInterLeftRule : InterPrfTy lpty rpty x -> lpty x
invInterLeftRule (lpf, _) = lpf

public export
invInterRightRule : InterPrfTy lpty rpty x -> rpty x
invInterRightRule (_, rpf) = rpf

public export
invInterNotLeftRule : (InterPrfTy lpty rpty x -> Void) -> rpty x ->
                      lpty x -> Void
invInterNotLeftRule pcontra rpf lpf = void (pcontra (lpf, rpf))

public export
invInterNotRightRule : (InterPrfTy lpty rpty x -> Void) -> lpty x ->
                       rpty x -> Void
invInterNotRightRule pcontra lpf rpf = void (pcontra (lpf, rpf))
