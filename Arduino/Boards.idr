module Arduino.Boards

import Arduino.Util

import Data.Vect
import Data.Vect.Quantifiers

%default total
%access public export

-- How arduino pins are designated in board
data Pin = D Nat
         | A Nat
         | DAC Nat

--- Particular hardware pins description ---

record UART_Info (guarantees : Pin -> Type) where
  constructor MkUartInfo
  TX, RX : Pin `BoundedWith` guarantees

record I2C_Info (guarantees : Pin -> Type) where
  constructor MkI2cInfo
  SDA, SCL : Pin `BoundedWith` guarantees

record SPI_Info (guarantees : Pin -> Type) where
  constructor MkSpiInfo
  MISO, MOSI, SCK, SS : Pin `BoundedWith` guarantees

--- The board-related info ---

record BitResolutionInfo where
  constructor MkBitResolutionInfo

  -- resolution in bits of underlying hardware
  hardwareResolution : Nat

  CanBeSetAsResolution : Nat -> Type

  -- resultion that is set after start or reset
  startupResolution : Nat `BoundedWith` CanBeSetAsResolution

record BoardInfo where
  constructor MkBoardInfo

  CanBeDigital : Pin -> Type
  CanBePWM     : Pin -> Type
  CanBeDAC     : Pin -> Type
  CanBeADC     : Pin -> Type

  bitResolutionPWN : BitResolutionInfo
  bitResolutionDAC : BitResolutionInfo
  bitResolutionADC : BitResolutionInfo

  CanBeInterrupt : Pin -> Type
  interruptForPin : (p : Pin) -> CanBeInterrupt p => Nat

  LED  : Pin `BoundedWith` CanBeDigital
  UART : KnownCountOf $ UART_Info CanBeDigital
  I2C  : KnownCountOf $ I2C_Info CanBeDigital
  SPI  : KnownCountOf $ SPI_Info CanBeDigital

  -- TODO pins in different lists of a single protocol should be different
  -- TODO should it be limited that peripheral pin of different protocols should not intersect?

record BoardState (board : BoardInfo) where
  constructor MkBoardState

  -- TODO add known info about pins
  -- TODO add known info about current resolutions for each group of analogish pins
