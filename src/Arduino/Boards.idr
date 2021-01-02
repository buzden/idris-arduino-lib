module Arduino.Boards

import public Arduino.Util

%default total

-----------------------
-----------------------
---  General stuff  ---
-----------------------
-----------------------

-- How arduino pins are designated in board
public export
data Pin = D Nat
         | A Nat
         | DAC Nat

public export
data PinPurpose = Input | Output

public export
data Board = BoardLabel String (Maybe String)

--------------------------------
--------------------------------
---   Binary digital stuff   ---
--------------------------------
--------------------------------

public export
data DigitalPinValue = Low | High

public export
interface HasDigitalPins (0 board : Board) where
  CanBeDigital : Pin -> Type

  lowLevelNumberForDigitalPin : (p : Pin) -> {auto cbd : CanBeDigital p} -> Bits8
  -- TODO To think, maybe use `Fin 256` instead?

--------------------
--- Built-in LED ---
--------------------

public export
interface HasDigitalPins board => HasBuiltIn_LED (0 board : Board) where
  LED : Pin

  Builtin_LED_IsDigital : CanBeDigital {board} LED

--------------------------------
--- Interrupt-realated stuff ---
--------------------------------

namespace Interrupts

  public export
  data InterruptEvent = Low | High | Change | Rising | Falling

  public export
  interface HasDigitalPins board => HasInterruptPins (0 board : Board) where
    CanBeInterrupt : Pin -> Type
    interruptForPin : (p : Pin) -> {auto cbi : CanBeInterrupt p} -> Nat
    PinSupportsMode : (p : Pin) -> {auto cbi : CanBeInterrupt p} -> InterruptEvent -> Type

    InterruptPinsAreDigital : (p : Pin) -> CanBeInterrupt p -> CanBeDigital {board} p

----------------------------
----------------------------
---   Analog-ish stuff   ---
----------------------------
----------------------------

namespace Analogish

  public export
  data AnalogType = PWM -- pulse-width modulation
                  | DAC -- digital-to-analog convertion
                  | ADC -- analog-to-digital convertion

  public export
  interface HasAnalogPins (0 typ : AnalogType) (0 board : Board) where
    CanBeAnalog : Pin -> Type

    lowLevelNumberForAnalogPin : (p : Pin) -> {auto cba : CanBeAnalog p} -> Bits8
    -- TODO To think, maybe use `Fin 256` instead?

    -- resolution in bits of underlying hardware
    HardwareResolution : Nat

    CanBeSetAsResolution : Nat -> Type

    -- resultion that is set after start or reset
    StartupResolution : Nat

    StartupResolutionCanBeSet : CanBeSetAsResolution StartupResolution
