module Arduino.Blink

import Arduino.Lib
import Arduino.Mega

main : IO ()
main = runArd Mega2560 $
  do pinMode LED Output
     forever $ do
       digitalWrite LED High
       delay 1000
       digitalWrite LED Low
       delay 2000
