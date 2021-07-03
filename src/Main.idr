module Main

-- import Data.List
import Data.Algebra.Set
import Data.Algebra.PointedSet
import Data.Algebra.UnarySystem
import Data.Algebra.Magma

-- Tests

testSet : Set
testSet = MkSet Integer (\x => x < 5)

testSet2 : Set
testSet2 = MkSet Integer (\x => x > 4)

testSet3 : Set
testSet3 = MkSet Integer (const True)


testPointedSet : PointedSet
testPointedSet = MkPointedSet testSet 4

testPointedSet2 : PointedSet
testPointedSet2 = MkPointedSet testSet2 5

testPointedSet3 : PointedSet
testPointedSet3 = MkPointedSet testSet3 0

testPointedMap : PointedMap Main.testPointedSet Main.testPointedSet2
testPointedMap = MkPointedMap (\x => x + 1)


testUnarySystem : UnarySystem
testUnarySystem = MkUnarySystem testSet3 (+ 1)


testMagma : Magma
testMagma = MkMagma testSet3 (+)



main : IO ()
main = do
  printLn (contains testSet 4)
  printLn (contains testSet 6)
  printLn (basepoint testPointedSet)
  printLn (pmap testPointedMap 0)
  printLn (pmap testPointedMap 4)
  printLn (unop testUnarySystem 6)
  printLn (binop testMagma 3 4)

  putStrLn "OK"
