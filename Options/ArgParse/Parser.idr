-- -------------------------------------------------------------- [ Parser.idr ]
-- Description : A simple parser for command options.
-- Copyright   : (c) Jan de Muijnck-Hughes
-- License     : see LICENSE
-- --------------------------------------------------------------------- [ EOH ]
module Options.ArgParse.Parser

import Options.ArgParse.Lexer
import Options.ArgParse.Parser.API

import Options.ArgParse.Model

%access private

-- ----------------------------------------------------------------- [ Parsers ]

flagLong : Rule Arg
flagLong = do
  l <- longFlag
  pure $ Flag l

flagShort : Rule Arg
flagShort = do
   s <- shortFlag
   pure $ Flag s

kvLong : Rule Arg
kvLong = do
    key <- longFlag
    equals
    value <- (arg <|> quoted)
    pure $ KeyValue key value

kvShort : Rule Arg
kvShort = do
    k <- shortFlag
    v <- (arg <|> quoted)
    pure $ KeyValue k v

options : Rule Arg
options = kvShort <|> kvLong <|> flagShort <|> flagLong <|> (do fs <- arg; pure $ File fs)

args : EmptyRule $ List Arg
args = do
    os <- many options
    pure $ os

public export
data ParseError = ParseFail String (Maybe (Int, Int)) (List Token)
                | LexFail (Int, Int, String)

export
Show ParseError where
  show (ParseFail err loc toks)
      = "Parse error: " ++ err ++ " at " ++ show loc ++ "\n" ++ show toks
  show (LexFail (c, l, str))
      = "Lex error at " ++ show (c, l) ++ " input: " ++ str

export
parseArgs : String -> Either ParseError (List Arg)
parseArgs str =
  case Lexer.lex str of
    Left err => Left (LexFail err)

    Right toks =>
      case parse args toks of

            Left (Error err []) =>
              Left $ ParseFail err Nothing []

            Left (Error err (t :: ts)) =>
              Left $ ParseFail err (Just (line t, col t))
                                   (map tok (t :: ts))
            Right (val, _) => Right val

-- --------------------------------------------------------------------- [ EOF ]
