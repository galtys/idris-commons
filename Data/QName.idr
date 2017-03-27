||| Lightweight representation of qualified names.
|||
||| TODO: Look at making names subject to user supplied predicates.
module Data.QName

import Data.Display

%default total
%access public export

data Ty = SIMPLE | QUALIFIED

data QName : (shape : Ty) -> Type where
  BN : String -> QName SIMPLE
  QN : String -> QName shape -> QName QUALIFIED

fromList : (xs : List String) -> (prf : NonEmpty xs) -> QName (if length xs > 1 then QUALIFIED else SIMPLE)
fromList (x :: []) IsNonEmpty = BN x
fromList (x :: (y :: xs)) IsNonEmpty with (nonEmpty xs)
  fromList (x :: (y :: xs)) IsNonEmpty | (Yes prf) =  QN x $ QN y $ fromList xs prf
  fromList (x :: (y :: xs)) IsNonEmpty | (No contra) = QN x $ BN y

fromList' : (xs : List String)
         -> {auto prf : NonEmpty xs}
         -> QName (if length xs > 1 then QUALIFIED else SIMPLE)
fromList' xs {prf} = fromList xs prf

Show (QName shape) where
  show (BN x)    = unwords ["BN", show x]
  show (QN x xs) = unwords ["QN", show x, show xs]

Display (QName shape) where
  display (BN x) = x
  display (QN x ys) = x ++ "." ++ display ys


-- --------------------------------------------------------------------- [ EOF ]
