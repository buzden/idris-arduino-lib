module Arduino.Mega

import Arduino.Boards
import Data.Fin

public export
Mega2560 : Board
Mega2560 = BoardLabel "mega" $ Just "atmega2560"

public export
data DigitalPinCondition : Pin -> Type where
  DD : (n : Fin 54) -> DigitalPinCondition $ D $ finToNat n
  AA : (n : Fin 16) -> DigitalPinCondition $ A $ finToNat n

public export
HasDigitalPins Mega2560 where
  CanBeDigital = DigitalPinCondition
  lowLevelNumberForDigitalPin (D _) {cbd=DD nn} = finToBits8 $ weakenN _ nn
  lowLevelNumberForDigitalPin (A _) {cbd=AA nn} = finToBits8 $ weakenN _ $ shift 54 nn

public export
HasBuiltIn_LED Mega2560 where
  LED = D 13
  Builtin_LED_IsDigital = DD 13
