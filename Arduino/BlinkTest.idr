import Arduino.Lib
import Arduino.Mega

import Data.Fin

%hint
x : Nat
x = 13

%hint
x' : Fin 54
x' = 13

%hint
y : Pin
y = D x

export
main : IO ()
main = runArd Mega2560 $ do
     pinMode (D 13) Output
     forever $ do
       digitalWrite (D 13) High
       delay 1000
       digitalWrite (D 13) Low
       delay 2000
