module Main

import Decidable.Equality

import Alpha.Algebra.Set
import Alpha.Algebra.Set as A

main : IO ()
main = do
  -- printLn (5 `elem` (MkFnSet (>5)))
  -- printLn (6 `elem` (MkFnSet (>5)))
  -- printLn (0 `elem` MkEmpty)
  -- printLn (0 `elem` MkUniverse)
  -- printLn (0 `elemEq` (MkSingleton 1))
  -- printLn (1 `elemEq` (MkSingleton 1))
  -- printLn (1 `elemEq` (MkHoled 1))
  -- printLn (0 `elemEq` (MkHoled 1))

  -- let s = MkFnSet (>5)
  --     s' = complement s
  -- printLn (6 `A.elem` (complement (MkFnSet (>5))))
  -- printLn (5 `A.elem` (complement (MkFnSet (>5))))

  putStrLn "OK"
