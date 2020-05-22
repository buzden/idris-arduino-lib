module Arduino.Mega

import Arduino.Boards

public export
Mega2560 : Board
Mega2560 = BoardLabel "mega" $ Just "atmega2560"

public export
data DigitalPinCondition : Pin -> Type where
  DD : (n : Nat) -> {auto ev : n `LTE` 53} -> DigitalPinCondition $ D n
  AA : (n : Nat) -> {auto ev : n `LTE` 15} -> DigitalPinCondition $ A n

public export
HasDigitalPins Mega2560 where
  CanBeDigital = DigitalPinCondition
  lowLevelNumberForDigitalPin (D n) = n
  lowLevelNumberForDigitalPin (A n) = n + 54

public export
HasBuiltIn_LED Mega2560 where
  LED = D 13
  Builtin_LED_IsDigital = DD _
