import Arduino.Coop
import Arduino.Raw

forever : Monad m => m a -> m b
forever x = do x; forever x

export
main : IO Unit
main = runCoop $ do
  pinMode 13 1
  pinMode 14 1
  (<||>)
    (forever $ do
      digitalWrite 13 1
      delayFor 1000
      digitalWrite 13 0
      delayFor 2000)
    (forever $ do
      digitalWrite 14 1
      delayFor 350
      digitalWrite 14 0
      delayFor 750)
