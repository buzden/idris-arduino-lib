import Arduino.Lib
import Arduino.Mega

%hint
x : Nat
x = 13

%hint
y : Pin
y = D x

-- For debug purpose only!
println : String -> Ard board (const Unit) NoFacts IO ()
println = ard . putStrLn

%hint
b : Board
b = Mega2560

LED' : {auto board : Board} -> HasBuiltIn_LED board => Pin
LED' {board} = LED {board}

main : IO ()
main = runArd Mega2560 $ do
     println "before all"
     pinMode LED' Output
     forever $ do
       println "\rforever block start"
       digitalWrite (D 13) High
       println "after high"
       delay 1000
       println "after delay 1"
       digitalWrite (D 13) Low
       println "after low"
       delay 2000
       println "after delay 2"
