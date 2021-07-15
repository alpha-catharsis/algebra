module Main

import Data.List.Elem
import Decidable.Equality

import Alpha.Algebra.Set
import Alpha.Algebra.Set as A

main : IO ()
main = do
  printLn (6 `A.elem` empty)
  printLn (6 `A.elem` universe)
  printLn (6 `A.elem` (singleton 5))
  printLn (6 `A.elem` (singleton 6))
  printLn (6 `A.elem` (holed 6))
  printLn (6 `A.elem` (holed 5))
  printLn (5 `A.elem` (propSet (>5)))
  printLn (6 `A.elem` (propSet (>5)))

  printLn ("******")

  printLn (6 `A.elem` (complement universe))
  printLn (6 `A.elem` (complement empty))
  printLn (6 `A.elem` (complement (singleton 6)))
  printLn (6 `A.elem` (complement (singleton 5)))
  printLn (6 `A.elem` (complement (holed 5)))
  printLn (6 `A.elem` (complement (holed 6)))
  printLn (6 `A.elem` (complement (propSet (>5))))
  printLn (5 `A.elem` (complement (propSet (>5))))

  printLn ("******")
  let s1 = intersection (propSet (>3)) (propSet (<5))
  printLn (3 `A.elem` s1)
  printLn (4 `A.elem` s1)
  printLn (5 `A.elem` s1)

  printLn ("******")
  let s2 = union (singleton 3) (singleton 5)
  printLn (3 `A.elem` s2)
  printLn (4 `A.elem` s2)
  printLn (5 `A.elem` s2)

  printLn ("******")
  let s3 = A.product (propSet (>3)) (singleton 5)
  printLn ((3,3) `A.elem` s3)
  printLn ((3,4) `A.elem` s3)
  printLn ((3,5) `A.elem` s3)
  printLn ((4,3) `A.elem` s3)
  printLn ((4,4) `A.elem` s3)
  printLn ((4,5) `A.elem` s3)
  printLn ((5,3) `A.elem` s3)
  printLn ((5,4) `A.elem` s3)
  printLn ((5,5) `A.elem` s3)

  printLn ("******")
  let s4 = coproduct (singleton 3) (singleton 4)
  printLn ((Left 3) `A.elem` s4)
  printLn ((Left 4) `A.elem` s4)
  printLn ((Right 3) `A.elem` s4)
  printLn ((Right 4) `A.elem` s4)

  printLn ("******")
  let s5 = difference (listSet [1,2,3]) (singleton 2)
  printLn (1 `A.elem` s5)
  printLn (2 `A.elem` s5)
  printLn (3 `A.elem` s5)

  putStrLn "OK"
