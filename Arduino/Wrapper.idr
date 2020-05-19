module Arduino.Wrapper

import Arduino.Boards
import Arduino.Util

import Control.Monad.Syntax

%default total
%access export

data Ard : (board : Board)
        -> (stateFun : BoardState -> Maybe BoardState) -- `Nothing` when board's state is not acceptable
        -> (m : Type -> Type) -> Type -> Type where
  Wrapped : m a -> Ard board stateFun m a

Functor m => Functor (Ard board stateFun m) where
  map f (Wrapped act) = Wrapped $ map f act

pure : Applicative m => a -> Ard board Prelude.Applicative.pure m a
pure = Wrapped . pure

(<*>) : Applicative m => Ard board sfL m (a -> b) -> Ard board sfR m a -> Ard board (sfL >=> sfR) m b
(Wrapped f) <*> (Wrapped x) = Wrapped $ f <*> x
