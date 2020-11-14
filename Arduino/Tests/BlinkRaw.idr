import Arduino.Raw

forever : Monad m => m a -> m b
forever x = do x; forever x

export
main : IO Unit
main = do
  pinMode 13 1
  forever $ do
    digitalWrite 13 1
    delayFor 1000
    digitalWrite 13 0
    delayFor 2000
