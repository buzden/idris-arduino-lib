module Arduino.Wrapper

import Arduino.Boards

%default total
%access export

data Ard : (board : Board)
        -> (statePrecondition : BoardState -> Type)
        -> (stateChanges : (inS : BoardState) -> statePrecondition inS => BoardState)
        -> (m : Type -> Type) -> Type -> Type where
  Wrapped : m a -> Ard board statePrecondition stateChanges m a

Functor m => Functor (Ard board statePrecondition stateChanges m) where
  map f (Wrapped act) = Wrapped $ map f act

pure : Applicative m => a -> Ard board (const Unit) (\s => s) m a
pure = Wrapped . pure
