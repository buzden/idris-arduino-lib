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
      delay 1000
      digitalWrite 13 0
      delay 2000)
    (forever $ do
      digitalWrite 14 1
      delay 350
      digitalWrite 14 0
      delay 750)
