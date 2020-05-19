module Arduino.Wrapper

%default total

--- Stuff copied from other modules ---

data Board = BoardLabel String (Maybe String)

BoardState : Type
BoardState = List (t : Type ** t) -- omnityped list of facts

data AndThen : (l : Type) -> (r : l -> Type) -> Type where
  ShortConj : (v : l) -> (w : r v) -> l `AndThen` r

--- The Wrapper stuff ---

data Ard : (board : Board)
        -> (statePrecondition : BoardState -> Type)
        -> (stateChanges : (inS : BoardState) -> statePrecondition inS -> BoardState)
        -> (m : Type -> Type) -> Type -> Type where
  Wrapped : m a -> Ard board statePrecondition stateChanges m a

Functor m => Functor (Ard board statePrecondition stateChanges m) where
  map f (Wrapped act) = Wrapped $ map f act

pure : Applicative m => a -> Ard board (const Unit) (\s, _ => s) m a
pure = Wrapped . pure

(<*>) : Applicative m => Ard board preL chL m (a -> b)
                      -> Ard board preR chR m a
                      -> Ard board (\inS => preL inS `AndThen` (preR . chL inS)) (\inS, (ShortConj l r) => chR (chL inS l) r) m b
(Wrapped f) <*> (Wrapped x) = Wrapped $ f <*> x
