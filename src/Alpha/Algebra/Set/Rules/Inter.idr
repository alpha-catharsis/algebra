---------------------
-- Module declaration
---------------------

module Alpha.Algebra.Set.Rules.Inter

-------------------
-- Internal imports
-------------------

import Alpha.Algebra.Set.Ops
import Alpha.Algebra.Set.Set

---------------------
-- Intersection rules
---------------------

public export
0 interRule : {lpty : SetPty a} -> {rpty : SetPty a} ->
              lpty x -> rpty x -> InterPty lpty rpty x
interRule lprf rprf = (lprf, rprf)

public export
0 interNotLeftRule : {lpty : SetPty a} -> Not (lpty x) ->
                     Not (InterPty lpty rpty x)
interNotLeftRule lcontra = lcontra . fst

interNotLeftElem : DisprovenElem lpty -> DisprovenElem (InterPty lpty rpty)
interNotLeftElem = projectElem (interNotLeftRule {lpty} {rpty})

public export
0 interNotRightRule : {rpty : SetPty a} -> Not (rpty x) ->
                      Not (InterPty lpty rpty x)
interNotRightRule rcontra = rcontra . snd

interNotRightElem : DisprovenElem rpty -> DisprovenElem (InterPty lpty rpty)
interNotRightElem = projectElem (interNotRightRule {lpty} {rpty})

public export
0 invInterLeftRule : InterPty lpty rpty x -> lpty x
invInterLeftRule = fst

public export
invInterLeftElem : ProvenElem (InterPty lpty rpty) -> ProvenElem lpty
invInterLeftElem = projectElem (invInterLeftRule {lpty} {rpty})

public export
0 invInterRightRule : InterPty lpty rpty x -> rpty x
invInterRightRule = snd

public export
invInterRightElem : ProvenElem (InterPty lpty rpty) -> ProvenElem rpty
invInterRightElem = projectElem (invInterRightRule {lpty} {rpty})

public export
0 invInterNotLeftRule : Not (InterPty lpty rpty x) -> rpty x ->
                        Not (lpty x)
invInterNotLeftRule pcontra rprf lprf = void (pcontra (lprf, rprf))

public export
0 invInterNotRightRule : Not (InterPty lpty rpty x) -> lpty x ->
                         Not (rpty x)
invInterNotRightRule pcontra lprf rprf = void (pcontra (lprf, rprf))
