module Commons.Data.FilePath

import Commons.Text.Display

%default total
%access public export


data FilePath : Type where
  Basename : (name : String)
          -> (ext  : Maybe String)
          -> FilePath
  Path : (name : String)
      -> (rest : FilePath)
      -> FilePath

fromList : (xs  : List String)
        -> (ext : Maybe String)
        -> (prf : NonEmpty xs)
        -> FilePath
fromList (x :: []) ext IsNonEmpty = Basename x ext
fromList (x :: (y :: xs)) ext IsNonEmpty with (nonEmpty xs)
  fromList (x :: (y :: xs)) ext IsNonEmpty | (Yes prf) = Path x $ Path y $ fromList xs ext prf
  fromList (x :: (y :: xs)) ext IsNonEmpty | (No contra) = Path x $ Basename y ext

fromList' : (xs  : List String)
         -> (ext : Maybe String)
         -> {auto prf : NonEmpty xs}
         -> FilePath
fromList' xs ext {prf} = fromList xs ext prf

Show FilePath where
  show (Basename n e) = unwords ["Basename", show n, show e]
  show (Path x xs)    = unwords ["Path", show x, show xs]


Display FilePath where
  display (Basename x Nothing)  = x
  display (Basename x (Just y)) = x ++ "." ++ y
  display (Path name rest)      = name ++ "/" ++ display rest
