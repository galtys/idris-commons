-- --------------------------------------------------------------- [ Error.idr ]
-- Module    : Error.idr
-- Copyright : (c) Jan de Muijnck-Hughes
-- License   : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]

module Commons.Options.ArgParse.Error

import public Commons.Options.ArgParse.Model
import public Commons.Options.ArgParse.Parser

%access public export

data ArgParseError : Type where
  InvalidOption : Arg -> ArgParseError
  ParseError : ParseError -> ArgParseError

(Show ParseError, Show Arg) => Show ArgParseError where
  show (InvalidOption o) = "Invalid Option " ++ show o
  show (ParseError err)  = "Parsing Error\n" ++ show err

-- --------------------------------------------------------------------- [ EOF ]
