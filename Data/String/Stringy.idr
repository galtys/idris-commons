module Data.String.Convert

%access public export
%default total

interface Stringy a where
  toString : a -> String
