module Arduino.Runner

import Arduino.Boards

import Data.Vect
import Data.Vect.Quantifiers

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

-- Yet execution is in rigid concrete type. No nice typeclasses, only combinators.
data Ard : (board : BoardInfo) -> BoardState board -> BoardState board -> Type -> Type where
  ArdAction : (board : BoardInfo) -> (inS, outS : BoardState board) -> IO a -> Ard board inS outS a
