module Arduino.Lib

import public Arduino.Boards
import public Arduino.Wrapper

%default total

namespace Raw
  %access private

  %include C "Arduino.h"

  digitalWrite : Int -> Int -> IO ()
  digitalWrite pin val = foreign FFI_C "digitalWrite" (Int -> Int -> IO ()) pin val

  pinMode : Int -> Int -> IO ()
  pinMode pin mode = foreign FFI_C "pinMode" (Int -> Int -> IO ()) pin mode

  delay : Int -> IO ()
  delay ms = foreign FFI_C "delay" (Int -> IO ()) ms

-- Note: functions naming was left to be (at least for now) as they were at the the original Arduino software.

-- For now, this function is meant to be used only with digital pins.
-- Also, for now, it is using `IO` directly under the `Ard`.
export
pinMode : {board : Board} -> {auto hdp : HasDigitalPins board}
       -> (pin : Pin) -> {auto cbd : CanBeDigital {board} pin}
       -> (purpose : PinPurpose)
       -> Ard board (const Unit) (oneFact pin purpose) IO ()
pinMode {board} {cbd} pin purpose = ard $ Raw.pinMode (toIntNat $ lowLevelNumberForDigitalPin {board} pin) (lowLevelNumberForPurpose purpose)
  where lowLevelNumberForPurpose : PinPurpose -> Int
        lowLevelNumberForPurpose Input  = 0
        lowLevelNumberForPurpose Output = 1

export
digitalWrite : {board : Board} -> {auto hdp : HasDigitalPins board}
            -> (pin : Pin) -> {auto cbd : CanBeDigital {board} pin}
            -> DigitalPinValue
            -> Ard board (LastFactEq pin Output) NoFacts IO ()
digitalWrite {board} {cbd} pin value = ard $ Raw.digitalWrite (toIntNat $ lowLevelNumberForDigitalPin {board} pin) (lowLevelNumberForValue value)
  where lowLevelNumberForValue : DigitalPinValue -> Int
        lowLevelNumberForValue Low  = 0
        lowLevelNumberForValue High = 1

-- TODO To use better representation for time.
-- TODO To think, whether time delay is a fact to represent at the typelevel or not.
export
delay : {board : Board} -> (microseconds : Nat) -> Ard board (const Unit) NoFacts IO ()
delay = ard . Raw.delay . toIntNat
