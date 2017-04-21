||| Module    : Action.idr
||| Copyright : (c) Jan de Muijnck-Hughes
||| License   : see LICENSE
|||
||| In some cases `Maybe` is not sufficient to describe the results of
||| operations. Here we describe a more Generic result data type.
module Data.Action

%access public export

||| Operations either return a success or some result, we use
||| `ActionTy` to differentiate between the two.
data ActionTy = SUCCESS | RESULT

||| A custom return type for operations.
|||
||| @aty What type of action are we performing.
||| @rty The return type for an action that returns a value.
||| @ety The error type for an action.
|||
data Action : (aty : ActionTy)
           -> (rty : Type)
           -> (ety : Type)
           -> Type
  where
    ||| The operation completed successfully and doesn't return a
    ||| result.
    Success : Action SUCCESS rty ety

    ||| The operation returns a result of type `rty`.
    |||
    ||| @rty The value returned.
    Result : rty -> Action RESULT rty ety

    ||| The operation failed and the given error was produced.
    |||
    ||| @ety The reported error.
    Error : ety -> Action aty rty ety


||| Given an `action` if it was successful return `success` otherwise return `backup`.
success : (backup  : Lazy b)
       -> (success : Lazy b)
       -> (action  : Action SUCCESS rty ety)
       -> b
success _      success Success   = success
success backup _       (Error x) = backup

||| Given an `action` if it was successful apply `transform` otherwise return `backup`.
result : (backup     : Lazy b)
      -> (transform  : Lazy (rty -> b))
      -> (result : Action RESULT rty ety)
      -> b
result _      transform (Result x) = transform x
result backup _         (Error x)  = backup

runEitherIO : IO (Either ety rty) -> IO $ Action RESULT rty ety
runEitherIO func =
  case !func of
    Left err  => pure $ Error  err
    Right res => pure $ Result res

(Show rty, Show ety) => Show (Action ty rty ety) where
  show Success    = "Success"
  show (Result x) = unwords ["Result", show x]
  show (Error  x) = unwords ["Error", show x]

-- --------------------------------------------------------------------- [ EOF ]
