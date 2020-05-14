module Arduino.Boards

import public Arduino.Util

%default total
%access public export

-----------------------
-----------------------
---  General stuff  ---
-----------------------
-----------------------

-- How arduino pins are designated in board
data Pin = D Nat
         | A Nat
         | DAC Nat

data PinPurpose = Input | Output

data Board = BoardLabel String (Maybe String)

--------------------------------
--------------------------------
---   Binary digital stuff   ---
--------------------------------
--------------------------------

data DigitalPinValue = Low | High

interface HasDigitalPins (board : Board) where
  CanBeDigital : Pin -> Type

  lowLevelNumberForDigitalPin : (p : Pin) -> CanBeDigital p => Nat

--------------------
--- Built-in LED ---
--------------------

interface HasDigitalPins board => HasBuiltIn_LED (board : Board) where
  LED : Pin

  Builtin_LED_IsDigital : CanBeDigital {board} LED

--------------------------------
--- Interrupt-realated stuff ---
--------------------------------

namespace Interrupts

  data InterruptEvent = Low | High | Change | Rising | Falling

  interface HasDigitalPins board => HasInterruptPins (board : Board) where
    CanBeInterrupt : Pin -> Type
    interruptForPin : (p : Pin) -> CanBeInterrupt p => Nat
    PinSupportsMode : (p : Pin) -> CanBeInterrupt p => InterruptEvent -> Type

    InterruptPinsAreDigital : (p : Pin) -> CanBeInterrupt p -> CanBeDigital {board} p

----------------------------
----------------------------
---   Analog-ish stuff   ---
----------------------------
----------------------------

namespace Analogish

  data AnalogType = PWM -- pulse-width modulation
                  | DAC -- digital-to-analog convertion
                  | ADC -- analog-to-digital convertion

  interface HasAnalogPins (typ : AnalogType) (board : Board) where
    CanBeAnalog : Pin -> Type

    lowLevelNumberForAnalogPin : (p : Pin) -> CanBeAnalog p => Nat

    -- resolution in bits of underlying hardware
    HardwareResolution : Nat

    CanBeSetAsResolution : Nat -> Type

    -- resultion that is set after start or reset
    StartupResolution : Nat

    StartupResolutionCanBeSet : CanBeSetAsResolution StartupResolution

-----------------------
-----------------------
---  General stuff  ---
-----------------------
-----------------------

BoardState : Type
BoardState = List (t : Type ** t) -- omnityped list of facts

CanBeJoined : BoardState -> BoardState -> Type
CanBeJoined = ?canBeJoined_rhs

JoinStateChanges : (ch1 : BoardState -> BoardState) -> (ch2 : BoardState -> BoardState) -> (inS : BoardState) -> CanBeJoined (ch1 inS) (ch2 inS) => BoardState
JoinStateChanges = ?joinStateChanges_rhs
