module Arduino.Raw

import Arduino.Coop
import public Arduino.Time
import Arduino.Util

%default total

public export
interface LowLevelArduino (m : Type -> Type) where
  digitalWrite : Bits8 -> Bits8 -> m ()
  pinMode      : Bits8 -> Bits8 -> m ()

%include C "Arduino.h"

export
LowLevelArduino IO where
  digitalWrite = foreign FFI_C "digitalWrite" (Bits8 -> Bits8 -> IO ())
  pinMode      = foreign FFI_C "pinMode"      (Bits8 -> Bits8 -> IO ())

export
DelayableFor IO where
  delay        = foreign FFI_C "delay"        (Int -> IO ()) . toMilliseconds

millis : IO Int
millis = foreign FFI_C "millis" (IO Int)

export
Timed IO where
  currentTime = map fromMilliseconds millis

export
LowLevelArduino m => LowLevelArduino (Coop m) where
  digitalWrite = lift .. digitalWrite
  pinMode      = lift .. pinMode
