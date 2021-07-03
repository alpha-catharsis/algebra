module Data.Algebra.PointedSet

import Data.Algebra.Set

public export
data PointedSet : Type where
  MkPointedSet : (s : Set) -> (x : setType s) ->
                 {auto prf : SetElem s x} -> PointedSet

public export
setType : PointedSet -> Type
setType (MkPointedSet s _) = setType s

public export
set : PointedSet -> Set
set (MkPointedSet s _) = s

public export
basepoint : (s : PointedSet) -> setType s
basepoint (MkPointedSet _ x) = x

public export
data PointedMap : (s : PointedSet) -> (s' : PointedSet) ->  Type where
  MkPointedMap : {s : PointedSet} -> {s' : PointedSet} ->
                 (f : setType s -> setType s') ->
                 {auto prf : f (basepoint s) = basepoint s'} -> PointedMap s s'

public export
pmap : {s : PointedSet} -> {s' : PointedSet} -> PointedMap s s' ->
       (setType s -> setType s')
pmap (MkPointedMap f) = f
