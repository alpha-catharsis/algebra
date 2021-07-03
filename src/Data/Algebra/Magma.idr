module Data.Algebra.Magma

import Data.Algebra.Set

public export
data Magma : Type where
  MkMagma : (s : Set) -> (f : setType s -> setType s -> setType s) ->
            {auto prf : (x : setType s) -> (y : setType s) ->
            (SetElem s (f x y))} -> Magma

public export
set : Magma -> Set
set (MkMagma s _) = s

public export
setType : Magma -> Type
setType = setType . set

public export
setOp : (s : Magma) -> (setType s -> setType s -> setType s)
setOp (MkMagma _ f) = f

public export
binop : (s : Magma) -> setType s -> setType s -> setType s
binop (MkMagma _ f) x y = f x y


public export
data MagmaMorphism : (s : Magma) -> (s' : Magma) ->  Type where
  MkMagmaMorphism : {s : Magma} -> {s' : Magma} ->
                    (f : setType s -> setType s') ->
                    {auto prf : (x : setType s) -> (y : setType s) ->
                    f (binop s x y) = binop s' (f x) (f y)} ->
                    MagmaMorphism s s'

public export
magmaMorphism : {s : Magma} -> {s' : Magma} -> MagmaMorphism s s' ->
                setType s -> setType s'
magmaMorphism (MkMagmaMorphism f) x = f x

public export
freeMagma : Type -> Magma
freeMagma a = MkMagma (treeSet a) MkBranch
