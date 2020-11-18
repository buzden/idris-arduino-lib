import Arduino.Raw

import Control.Monad.Coop

forever : Monad m => m a -> m b
forever x = do x; forever x

export
main : IO Unit
main = runCoop $ do
  pinMode 3 1
  digitalWrite 3 1
  sleepFor 1000
  digitalWrite 3 0
  pinMode 13 1
  pinMode 6 1
  (<||>)
    (forever $ do
      digitalWrite 13 1
      sleepFor 1000
      digitalWrite 13 0
      sleepFor 2000)
    (forever $ do
      digitalWrite 6 1
      sleepFor 350
      digitalWrite 6 0
      sleepFor 750)
