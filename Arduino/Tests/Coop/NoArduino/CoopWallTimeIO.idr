import Arduino.Coop

import Debug.Trace

import System.Clock

millis : HasIO io => io Integer
millis = liftIO $ composeTime <$> clockTime Monotonic where
  composeTime : Clock Monotonic -> Integer
  composeTime (MkClock secs nanos) = secs * 1000 + nanos `div` 1000000

Debug IO where
  debug msg = trace msg $ pure ()

Timed IO where
  currentTime = fromInteger <$> millis

printTime : (offset : Integer) -> String -> Coop IO Unit
printTime offset s = debugInfo ("printTime " ++ s) $ printLn $ "[time: " ++ show (!millis - offset) ++ "] " ++ s

forever : Monad m => m a -> m b
forever x = do x; forever x

export
main : IO Unit
main = do printLn "before coop"
          runCoop $ do
  offset <- debugInfo "first millis" $ millis
  printTime offset "start"
  (<||>)
    (forever $ do
      printTime offset "proc 1, before 1000"
      delayFor 1000
      printTime offset "proc 1, before 2000"
      delayFor 2000)
    (forever $ do
      printTime offset "proc 2, before 350"
      delayFor 350
      printTime offset "proc 2, before 750"
      delayFor 750)

