module Alpha.Data.Tree

public export
data Tree : Type -> Type where
  MkLeaf : a -> Tree a
  MkBranch : Tree a -> Tree a -> Tree a
