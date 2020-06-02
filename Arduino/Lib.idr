module Arduino.Lib

import public Arduino.Boards
import Arduino.Raw
import public Arduino.Time
import public Arduino.Wrapper

%default total

-- Note: functions naming was left to be (at least for now) as they were at the the original Arduino software.

-- For now, this function is meant to be used only with digital pins.
-- Also, for now, it is using `IO` directly under the `Ard`.
export
pinMode : {board : Board} -> {auto hdp : HasDigitalPins board}
       -> (pin : Pin) -> {auto cbd : CanBeDigital {board} pin}
       -> (purpose : PinPurpose)
       -> Ard board (const Unit) (oneFact pin purpose) IO ()
pinMode {board} {cbd} pin purpose = ard $ Arduino.Raw.pinMode (lowLevelNumberForDigitalPin {board} pin) (lowLevelNumberForPurpose purpose)
  where lowLevelNumberForPurpose : PinPurpose -> Bits8
        lowLevelNumberForPurpose Input  = 0
        lowLevelNumberForPurpose Output = 1

export
digitalWrite : {board : Board} -> {auto hdp : HasDigitalPins board}
            -> (pin : Pin) -> {auto cbd : CanBeDigital {board} pin}
            -> DigitalPinValue
            -> Ard board (LastFactEq pin Output) NoFacts IO ()
digitalWrite {board} {cbd} pin value = ard $ Arduino.Raw.digitalWrite (lowLevelNumberForDigitalPin {board} pin) (lowLevelNumberForValue value)
  where lowLevelNumberForValue : DigitalPinValue -> Bits8
        lowLevelNumberForValue Low  = 0
        lowLevelNumberForValue High = 1

-- TODO To think, whether time delay is a fact to represent at the typelevel or not.
export
delay : {board : Board} -> Time -> Ard board (const Unit) NoFacts IO ()
delay = ard . Arduino.Time.delay
