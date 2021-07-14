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

  printLn ("******")

  printLn (6 `elem` (complement universe))
  printLn (6 `elem` (complement empty))
  printLn (6 `elem` (complement (singleton 6)))
  printLn (6 `elem` (complement (singleton 5)))
  printLn (6 `elem` (complement (holed 5)))
  printLn (6 `elem` (complement (holed 6)))
  printLn (6 `elem` (complement (fnSet (>5))))
  printLn (5 `elem` (complement (fnSet (>5))))

  printLn ("******")
  let s1 = intersection (fnSet (>3)) (fnSet (<5))
  printLn (3 `elem` s1)
  printLn (4 `elem` s1)
  printLn (5 `elem` s1)

  printLn ("******")
  let s2 = union (singleton 3) (singleton 5)
  printLn (3 `elem` s2)
  printLn (4 `elem` s2)
  printLn (5 `elem` s2)

  printLn ("******")
  let s3 = A.product (fnSet (>3)) (fnSet (<5))
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

  putStrLn "OK"
