module Commons.ST

import Control.ST

import Data.Action

%default total
%access public export

addIfResult : Type -> Action (Action RESULT Var ety)
addIfResult ty = Add (result Nil (\var => [var ::: ty]))

onAction : a -> a -> Action aty rty ety -> a
onAction x y Success    = x
onAction x y (Result _) = x
onAction x y (Error _)  = y


-- --------------------------------------------------------------------- [ EOF ]
