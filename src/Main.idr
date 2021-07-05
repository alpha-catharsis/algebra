module Main

import Alpha.Algebra.Set


main : IO ()
main = do
  printLn (contains (MkSet (> 5)) 5)
  printLn (contains (MkSet (> 5)) 6)
  printLn (contains emptySet 5)
  printLn (contains universeSet 5)
  printLn (contains (singletonSet 1) 0)
  printLn (contains (singletonSet 1) 1)
  printLn (contains (complement (MkSet (> 5))) 5)
  printLn (contains (complement (MkSet (> 5))) 6)
  putStrLn "OK"
