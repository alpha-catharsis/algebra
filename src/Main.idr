module Main

-- import Data.List
import Alpha.Algebra.Op
import Alpha.Algebra.Set
import Alpha.Algebra.PointedSet
import Alpha.Algebra.UnarySystem
import Alpha.Algebra.Magma

-- Tests

testSet : Set Integer
testSet = MkSet (> 5)

testPointedSet : PointedSet Integer
testPointedSet = MkPointedSet testSet 6

testPointedSet2 : PointedSet Integer
testPointedSet2 = MkPointedSet testSet 7

testPointedMap : PointedMap Main.testPointedSet Main.testPointedSet2
testPointedMap = MkPointedMap (+1)

testUnarySystem : UnarySystem Integer
testUnarySystem = MkUnarySystem universeSet (the (UnOp Integer) (+1))

main : IO ()
main = do
  printLn (contains testSet 5)
  printLn (contains testSet 6)
  printLn (basepoint testPointedSet)
  printLn (basepoint testPointedSet2)
  printLn (pmap testPointedMap 4)
  printLn (unop testUnarySystem 0)
  putStrLn "OK"
