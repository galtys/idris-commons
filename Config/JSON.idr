module Config.JSON

import Data.PList

import Text.Token
import Text.Lexer
import Text.Parser

import Language.JSON.Lexer

import public Config.JSON.Model

import Config.JSON.Parser

%default total
%access public export


fromString : String -> Maybe (JSONDoc DOC)
fromString src with (lexJSON src)
  fromString src | Nothing = Nothing
  fromString src | (Just x) with (parseJSON x)
    fromString src | (Just x) | Nothing = Nothing
    fromString src | (Just x) | (Just y) = Just y



-- --------------------------------------------------------------------- [ EOF ]
