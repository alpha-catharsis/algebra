module Main

import Data.List.Elem
import Decidable.Equality

import Alpha.Algebra.Set
import Alpha.Algebra.Set.Set as A
import Alpha.Algebra.Relation

main : IO ()
main = do
  printLn (6 `elem` (MkEmptySet Integer))
  printLn (6 `elem` (MkUniverseSet Integer))
  printLn (6 `elem` (MkSingletonSet 5))
  printLn (6 `elem` (MkSingletonSet 6))
  printLn (6 `elem` (MkHoledSet 6))
  printLn (6 `elem` (MkHoledSet 5))
  printLn (5 `elem` (MkPropSet (>5)))
  printLn (6 `elem` (MkPropSet (>5)))
  printLn (5 `A.elem` [1,2,3])

  printLn ("******")

  printLn (6 `elem` (MkComplement (MkUniverseSet Integer)))
  printLn (6 `elem` (MkComplement (MkEmptySet Integer)))
  printLn (6 `elem` (MkComplement (MkSingletonSet 6)))
  printLn (6 `elem` (MkComplement (MkSingletonSet 5)))
  printLn (6 `elem` (MkComplement (MkHoledSet 5)))
  printLn (6 `elem` (MkComplement (MkHoledSet 6)))
  printLn (6 `elem` (MkComplement (MkPropSet (>5))))
  printLn (5 `elem` (MkComplement (MkPropSet (>5))))

  printLn ("******")
  let s1 = MkIntersection (MkPropSet (>3)) (MkPropSet (<5))
  printLn (3 `elem` s1)
  printLn (4 `elem` s1)
  printLn (5 `elem` s1)

  printLn ("******")
  let s2 = MkUnion (MkSingletonSet 3) (MkSingletonSet 5)
  printLn (3 `elem` s2)
  printLn (4 `elem` s2)
  printLn (5 `elem` s2)

  printLn ("******")
  let s3 = MkProduct (MkPropSet (>3)) (MkSingletonSet 5)
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
  let s4 = MkCoproduct (MkSingletonSet 3) (MkSingletonSet 4)
  printLn ((Left 3) `elem` s4)
  printLn ((Left 4) `elem` s4)
  printLn ((Right 3) `elem` s4)
  printLn ((Right 4) `elem` s4)

  printLn ("******")
  let s5 = difference [1,2,3] (MkSingletonSet 2)
  printLn (1 `elem` s5)
  printLn (2 `elem` s5)
  printLn (3 `elem` s5)

  printLn ("******")
  let s6 = MkSingletonSet 5
  printLn (basepoint s6 {a=Integer})
  printLn ((basepoint s6) `elem` s6)

  printLn ("******")
  printLn (subset (MkEmptySet Integer) (MkSingletonSet 5))
  printLn (subset (MkSingletonSet 5) (MkUniverseSet Integer))

  putStrLn "OK"
