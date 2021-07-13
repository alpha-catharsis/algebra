module Main

import Decidable.Equality

import Alpha.Algebra.Set
import Alpha.Algebra.Set as A

main : IO ()
main = do
  printLn (6 `elem` empty)
  printLn (6 `elem` universe)
  printLn (6 `elem` (singleton 5))
  printLn (6 `elem` (singleton 6))
  printLn (6 `elem` (holed 6))
  printLn (6 `elem` (holed 5))
  printLn (5 `elem` (fnSet (>5)))
  printLn (6 `elem` (fnSet (>5)))
  putStrLn "OK"
