module Data.Display

%access public export
%default total

||| Present a version `String` of `a` for display.
|||
||| By default `Display` displays `a`s `Show` instance.
|||
||| Unlike `Show` there is no link to `Read`, and should see this as
||| inbetween `Pretty` and `Show`, that is useful for adhoc `toString`
||| methods.
interface Display a where
  display : a -> String

namespace IO
  display : Display a => a -> IO ()
  display x = putStr $ display x

  displayLn : Display a => a -> IO ()
  displayLn x = putStrLn $ display x
