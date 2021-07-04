module Alpha.Algebra.Magma

-- import Alpha.Algebra.Func
-- import Alpha.Algebra.Op
-- import Alpha.Algebra.Set
-- import Alpha.Data.Tree

-- public export
-- data Magma : Type -> Type where
--   MkMagma : (s : Set t) -> (f : BinOp t) ->
--             {auto prf : ClosedBinOp f s} ->
--             Magma t

-- public export
-- set : Magma t -> Set t
-- set (MkMagma s _) = s

-- public export
-- binop : Magma t -> BinOp t
-- binop (MkMagma _ f) = f

-- public export
-- data MagmaMorphism : (s : Magma t) -> (s' : Magma u) -> Type where
--   MkMagmaMorphism : {s : Magma t} -> {s' : Magma u} ->
--                     (f : UnFunc t u) ->
--                     {auto prf : TotalUnFunc f (set s) (set s')} ->
--                     {auto prf : Morphism f (binop s) (binop s')} ->
--                     MagmaMorphism s s'

-- public export
-- magmaMorphism : {s : Magma t} -> {s' : Magma u} -> MagmaMorphism s s' ->
--                 t -> u
-- magmaMorphism (MkMagmaMorphism f) x = f x

-- public export
-- freeMagma : (t : Type) -> Magma (Tree t)
-- freeMagma a = MkMagma universeSet MkBranch
