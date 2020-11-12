module Arduino.Raw

import Arduino.Coop
import public Arduino.Time
import Arduino.Util

import Control.Monad.Trans

%default total

-----------------
--- Interface ---
-----------------

public export
interface LowLevelArduino (m : Type -> Type) where
  digitalWrite : Bits8 -> Bits8 -> m Unit
  pinMode      : Bits8 -> Bits8 -> m Unit

---------------------------------------
--- Real (hardware) implementations ---
---------------------------------------

%foreign "C:digitalWrite,libarduino"
prim_digitalWrite : Bits8 -> Bits8 -> PrimIO Unit

%foreign "C:pinMode,libarduino"
prim_pinMode : Bits8 -> Bits8 -> PrimIO Unit

export
LowLevelArduino IO where
  digitalWrite = primIO ... prim_digitalWrite
  pinMode      = primIO ... prim_pinMode

%foreign "C:delay,libarduino"
prim_delay : Bits32 -> PrimIO Unit

export
DelayableFor IO where
  delay = primIO . prim_delay . toMilliseconds

%foreign "C:millis,libarduino"
prim_millis : PrimIO Bits32

export
Timed IO where
  currentTime = fromMilliseconds <$> primIO prim_millis

-------------------------------
--- Lifting implementations ---
-------------------------------

export
(LowLevelArduino m, Monad m) => LowLevelArduino (Coop m) where
  digitalWrite = lift ... digitalWrite
  pinMode      = lift ... pinMode
