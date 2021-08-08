module Main

import Data.List.Elem
import Decidable.Equality

import Alpha.Algebra.Function
import Alpha.Algebra.Set

main : IO ()
main = do
  printLn (6 `elem` emptySet)
  printLn (6 `elem` universeSet)
  printLn (6 `elem` (singletonSet 5))
  printLn (6 `elem` (singletonSet 6))
  printLn (6 `elem` (holedSet 6))
  printLn (6 `elem` (holedSet 5))
  printLn (5 `elem` (propSet (>5)))
  printLn (6 `elem` (propSet (>5)))

  printLn ("******")

  printLn (6 `elem` (complement universeSet))
  printLn (6 `elem` (complement emptySet))
  printLn (6 `elem` (complement (singletonSet 6)))
  printLn (6 `elem` (complement (singletonSet 5)))
  printLn (6 `elem` (complement (holedSet 5)))
  printLn (6 `elem` (complement (holedSet 6)))
  printLn (6 `elem` (complement (propSet (>5))))
  printLn (5 `elem` (complement (propSet (>5))))

  printLn ("******")
  let s1 = intersection (propSet (>3)) (propSet (<5))
  printLn (3 `elem` s1)
  printLn (4 `elem` s1)
  printLn (5 `elem` s1)

  printLn ("******")
  let s2 = union (singletonSet 3) (singletonSet 5)
  printLn (3 `elem` s2)
  printLn (4 `elem` s2)
  printLn (5 `elem` s2)

  printLn ("******")
  let s3 = product (propSet (>3)) (singletonSet 5)
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
  let s4 = coproduct (singletonSet 3) (singletonSet 4)
  printLn ((Left 3) `elem` s4)
  printLn ((Left 4) `elem` s4)
  printLn ((Right 3) `elem` s4)
  printLn ((Right 4) `elem` s4)

  printLn ("******")
  let s5 = difference (listSet [1,2,3]) (singletonSet 2)
  printLn (1 `elem` s5)
  printLn (2 `elem` s5)
  printLn (3 `elem` s5)

  -- printLn ("******")
  -- let s6 = singletonPointedSet (singletonSet 5)
  -- printLn (basepoint s6)
  -- printLn (6 `elem` (setDec s6))
  -- printLn (5 `elem` (setDec s6))

  -- printLn ("******")
  -- let s7 = UniversePointedSet 1
  -- printLn (basepoint s7)
  -- printLn (0 `elem` (setDec s7))
  -- printLn (1 `elem` (setDec s7))

  -- printLn ("******")
  -- let s8 = propPointedSet (propSet (> 5) {a=Integer}) 6
  -- printLn (basepoint s8)
  -- printLn (5 `elem` (setDec s8))
  -- printLn (6 `elem` (setDec s8))

  -- printLn ("******")
  -- let s9 = listPointedSet (listSet [1,2,3]) 2
  -- printLn (basepoint s9)
  -- printLn (4 `elem` (setDec s9))
  -- printLn (3 `elem` (setDec s9))



  putStrLn "OK"
