module Main

import Data.List.Elem
import Decidable.Equality

import Alpha.Algebra.Set

main : IO ()
main = do
  printLn (6 `elem` emptySet)
  printLn (6 `elem` universeSet)
  printLn (6 `elem` (singleton 5))
  printLn (6 `elem` (singleton 6))
  printLn (6 `elem` (holed 6))
  printLn (6 `elem` (holed 5))
  printLn (5 `elem` (propSet (>5)))
  printLn (6 `elem` (propSet (>5)))

  printLn ("******")

  printLn (6 `elem` (complement universeSet))
  printLn (6 `elem` (complement emptySet))
  printLn (6 `elem` (complement (singleton 6)))
  printLn (6 `elem` (complement (singleton 5)))
  printLn (6 `elem` (complement (holed 5)))
  printLn (6 `elem` (complement (holed 6)))
  printLn (6 `elem` (complement (propSet (>5))))
  printLn (5 `elem` (complement (propSet (>5))))

  printLn ("******")
  let s1 = intersection (propSet (>3)) (propSet (<5))
  printLn (3 `elem` s1)
  printLn (4 `elem` s1)
  printLn (5 `elem` s1)

  printLn ("******")
  let s2 = union (singleton 3) (singleton 5)
  printLn (3 `elem` s2)
  printLn (4 `elem` s2)
  printLn (5 `elem` s2)

  printLn ("******")
  let s3 = ProductOps.product (propSet (>3)) (singleton 5)
  printLn ((3,3) `elem` s3)
  printLn ((3,4) `elem` s3)
  printLn ((3,5) `elem` s3)
  printLn ((4,3) `elem` s3)
  printLn ((4,4) `elem` s3)
  printLn ((4,5) `elem` s3)
  printLn ((5,3) `elem` s3)
  printLn ((5,4) `elem` s3)
  printLn ((5,5) `elem` s3)

  printLn ("******")
  let s4 = coproduct (singleton 3) (singleton 4)
  printLn ((Left 3) `elem` s4)
  printLn ((Left 4) `elem` s4)
  printLn ((Right 3) `elem` s4)
  printLn ((Right 4) `elem` s4)

  printLn ("******")
  let s5 = difference (listSet [1,2,3]) (singleton 2)
  printLn (1 `elem` s5)
  printLn (2 `elem` s5)
  printLn (3 `elem` s5)

  putStrLn "OK"
