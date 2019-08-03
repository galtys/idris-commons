module Text.Lexer.Run

import Data.Location
import Text.Lexer

%default total
%access public export


public export
record LexError where
  constructor MkLexFail
  location : Location
  input  : String

public export
data LexFail = LError LexError | LIOErr FileError

public export
record Lexer a where
  constructor MkLexer
  tokenMap : TokenMap a
  keep : TokenData a -> Bool

export
lexString : Lexer a
         -> String
         -> Either LexError (List (TokenData a))
lexString lexer str =
      case Lexer.Core.lex (tokenMap lexer) str of
        (tok, (_, _, "")) => Right (filter (keep lexer) tok)
        (_,   (c,l,i))    => Left (MkLexFail (MkLoc Nothing (toNat c) (toNat l)) i)

export
lexFile : Lexer a -> String -> IO $ Either LexFail (List (TokenData a))
lexFile lexer fname = do
  Right str <- readFile fname | Left err => pure (Left (LIOErr err))
  case lexString lexer str of
        Left err => pure $ Left (LError (record {location->source = Just fname} err))
        Right toks => pure (Right toks)
