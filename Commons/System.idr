module Commons.System

import System

import Control.IOExcept
import Control.ST

import Data.So

public export
interface SystemIO (m : Type -> Type) where
  getArgs : STrans m (List String) xs (const xs)
  time    : STrans m Integer       xs (const xs)
  usleep  : (i : Int) -> { auto prf : So (i >= 0 && i <= 1000000) } -> STrans m () xs (const xs)

export
SystemIO IO where
  getArgs = lift getArgs
  time    = lift time
  usleep  i = lift (usleep i)

SystemIO (IOExcept err) where
  getArgs = lift (ioe_lift getArgs)
  time    = lift (ioe_lift time)
  usleep  i = lift (ioe_lift $ usleep i)

-- --------------------------------------------------------------------- [ EOF ]
