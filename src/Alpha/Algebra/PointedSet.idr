module Alpha.Algebra.PointedSet

import Alpha.Algebra.Set

public export
data PointedSet : Type -> Type where
  MkPointedSet : (s : Set t) -> (x : t) ->
                 {auto prf : SetElem s x} -> PointedSet t

public export
set : PointedSet t -> Set t
set (MkPointedSet s _) = s

public export
basepoint : PointedSet t -> t
basepoint (MkPointedSet _ x) = x

public export
data PointedMap : (s : PointedSet t) -> (s' : PointedSet u) ->  Type where
  MkPointedMap : {0 s : PointedSet t} -> {0 s' : PointedSet u} ->
                 (f : t -> u) ->
                 {auto 0 prf : f (basepoint s) = basepoint s'} ->
                 PointedMap s s'

public export
pmap : {s : PointedSet t} -> {s' : PointedSet u} -> PointedMap s s' -> (t -> u)
pmap (MkPointedMap f) = f
