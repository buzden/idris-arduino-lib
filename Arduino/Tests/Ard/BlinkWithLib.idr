import Arduino.Lib
import Arduino.Mega

%hint
x : Nat
x = 13

%hint
y : Pin
y = D x

export
main : IO Unit
main = runArd Mega2560 $ do
     pinMode (D 13) Output
     forever $ do
       digitalWrite (D 13) High
       delay 1000
       digitalWrite (D 13) Low
       delay 2000
