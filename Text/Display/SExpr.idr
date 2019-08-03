module Text.Display.SExpr

import Data.Vect

%default total
%access export

public export
interface SExpr a where
  toSExpr : a -> String

display : SExpr a => a -> IO ()
display = (putStr . toSExpr)

displayLn : SExpr a => a -> IO ()
displayLn = (putStrLn . toSExpr)

atom : Show a => (tag : String) -> a -> String
atom tag x = with List concat ["(", tag, " ", show x, ")"]

atomStr : (tag : String) -> String -> String
atomStr tag x = with List concat ["(", tag, " ", x, ")"]

compound : SExpr a => (tag : String) -> a -> String
compound tag x = with List concat ["(", tag, " ", toSExpr x, ")"]


SExpr String where
  toSExpr = atom "String"

SExpr Nat where
  toSExpr = atom "Nat"

SExpr Integer where
  toSExpr = atom "Integer"

SExpr a => SExpr (List a) where
  toSExpr xs = atomStr "List" (unwords $ map toSExpr xs)

SExpr a => SExpr (Vect n a) where
  toSExpr xs =  atomStr "Vect" (unwords $ toList $ map toSExpr xs)
