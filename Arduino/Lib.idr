module Arduino.Lib

import public Arduino.Boards
import public Arduino.Wrapper

%default total
%access export

namespace Raw
  %access private

  %include C "Arduino.h"

  digitalWrite : Int -> Int -> IO ()
  digitalWrite pin val = foreign FFI_C "digitalWrite" (Int -> Int -> IO ()) pin val

  pinMode : Int -> Int -> IO ()
  pinMode pin mode = foreign FFI_C "pinMode" (Int -> Int -> IO ()) pin mode

  delay : Int -> IO ()
  delay ms = foreign FFI_C "delay" (Int -> IO ()) ms

-- TODO to add all those functions wrapped (returning actions wrapped in `Arduino` "parameterized monad")
