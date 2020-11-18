||| This module is about *aliases* for pins that belong to some hardware protocol (bus)
module Arduino.Protocols

import Arduino.Boards

import Data.Vect
import Data.Vect.Quantifiers

%default total
%access public export

-----------------
--- Protocols ---
-----------------

-- TODO to think whether can pins used in different protocols intersect with each other?
-- TODO to think why digital, PWM, DAC and ADC are not just yet another protocols?

record HardwareProtocol where
  constructor MkProtocol
  protocolName : String
  protocolPinsCount : Nat

interface HasDigitalPins board => HasProtocol (prot : HardwareProtocol) (board : Board) where
  ProtocolPinGroupsCount : Nat

  ProtocolPins : Fin ProtocolPinGroupsCount -> Vect (protocolPinsCount prot) Pin

  AllProtocolPins : Vect (ProtocolPinGroupsCount * protocolPinsCount prot) Pin
  AllProtocolPins = ?flattenSomehow -- map ProtocolPins (allFinsTo ProtocolPinGroupsCount)
    where
      allFinsTo : (n : Nat) -> Vect n (Fin n)
      allFinsTo Z     = []
      allFinsTo (S n) = last :: map weaken (allFinsTo n)

  AllProtocolPinsDigital : All (CanBeDigital {board}) AllProtocolPins
  AllProtocolPinsDifferent : AllDiffer AllProtocolPins

--- UART ---

UART : HardwareProtocol
UART = MkProtocol "UART" 2

TX : HasProtocol UART board => Fin (ProtocolPinGroupsCount {prot=UART} {board}) -> Pin
RX : HasProtocol UART board => Fin (ProtocolPinGroupsCount {prot=UART} {board}) -> Pin

TX {board} = Data.Vect.index 0 . ProtocolPins {prot=UART} {board}
RX {board} = Data.Vect.index 1 . ProtocolPins {prot=UART} {board}

--- I2C ---

I2C : HardwareProtocol
I2C = MkProtocol "I2C" 2

SDA : HasProtocol I2C board => Fin (ProtocolPinGroupsCount {prot=I2C} {board}) -> Pin
SCL : HasProtocol I2C board => Fin (ProtocolPinGroupsCount {prot=I2C} {board}) -> Pin

SDA {board} = Data.Vect.index 0 . ProtocolPins {prot=I2C} {board}
SCL {board} = Data.Vect.index 1 . ProtocolPins {prot=I2C} {board}

--- SPI ---

SPI : HardwareProtocol
SPI = MkProtocol "SPI" 4

MISO : HasProtocol SPI board => Fin (ProtocolPinGroupsCount {prot=SPI} {board}) -> Pin
MOSI : HasProtocol SPI board => Fin (ProtocolPinGroupsCount {prot=SPI} {board}) -> Pin
SCK  : HasProtocol SPI board => Fin (ProtocolPinGroupsCount {prot=SPI} {board}) -> Pin
SS   : HasProtocol SPI board => Fin (ProtocolPinGroupsCount {prot=SPI} {board}) -> Pin

MISO {board} = Data.Vect.index 0 . ProtocolPins {prot=SPI} {board}
MOSI {board} = Data.Vect.index 1 . ProtocolPins {prot=SPI} {board}
SCK  {board} = Data.Vect.index 2 . ProtocolPins {prot=SPI} {board}
SS   {board} = Data.Vect.index 3 . ProtocolPins {prot=SPI} {board}
