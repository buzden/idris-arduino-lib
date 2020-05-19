module Arduino.Wrapper

import Arduino.Boards
import Arduino.Util

import Control.Monad.Syntax

%default total
%access export

----------------------------------------------------------------------
--- Data structure embedding effect and its type-level description ---
----------------------------------------------------------------------

data Ard : (board : Board)
        -> (stateFun : BoardState -> Maybe BoardState) -- `Nothing` when board's state is not acceptable
        -> (m : Type -> Type) -> Type -> Type where
  Wrapped : m a -> Ard board stateFun m a

-------------------------
--- Functor for `Ard` ---
-------------------------

Functor m => Functor (Ard board stateFun m) where
  map f (Wrapped act) = Wrapped $ map f act

--------------------------------------------
--- Applicative-like functions for `Ard` ---
--------------------------------------------

pure : Applicative m => a -> Ard board Prelude.Applicative.pure m a
pure = Wrapped . pure

(<*>) : Applicative m => Ard board sfL m (a -> b) -> Ard board sfR m a -> Ard board (sfL >=> sfR) m b
(Wrapped f) <*> (Wrapped x) = Wrapped $ f <*> x

--- Additional applicative-like syntax ---

(*>) : Applicative m => Ard board sfL m a -> Ard board sfR m b -> Ard board (sfL >=> sfR) m b
(Wrapped l) *> (Wrapped r) = Wrapped $ l *> r

(<*) : Applicative m => Ard board sfL m a -> Ard board sfR m b -> Ard board (sfL >=> sfR) m a
(Wrapped l) <* (Wrapped r) = Wrapped $ l <* r

--------------------------------------------
--- Alternative-like functions for `Ard` ---
--------------------------------------------

-- TODO to think whether `Applicative.pure` is a correct state change parameter for the `empty` action.
empty : Alternative m => Ard board Prelude.Applicative.pure m a
empty = Wrapped $ empty

-- The following function is a workarond of a compiler bug, which you run into when inline it.
public export
CombineMaybeBoardStates : BoardState -> Maybe BoardState -> Maybe BoardState -> Maybe BoardState
CombineMaybeBoardStates original ml mr = CombineBoardStates original !ml !mr

(<|>) : Alternative m => Ard board sfL m a
                      -> Ard board sfR m a
                      -> Ard board (\st => CombineMaybeBoardStates st (sfL st) (sfR st)) m a
(Wrapped l) <|> (Wrapped r) = Wrapped $ l <|> r

--------------------------------------
--- Monad-like functions for `Ard` ---
--------------------------------------

(>>=) : Monad m => Ard board sfL m a -> (a -> Ard board sfR m b) -> Ard board (sfL >=> sfR) m b
(Wrapped l) >>= f = Wrapped $ l >>= \x => let Wrapped r = f x in r

join : Monad m => Ard board sfL m (Ard board sfR m a) -> Ard board (sfL >=> sfR) m a
join (Wrapped l) = Wrapped $ l >>= \ard => let Wrapped r = ard in r

--- Additional monad-like syntax ---

(=<<) : Monad m => (a -> Ard board sfR m b) -> Ard board sfL m a -> Ard board (sfL >=> sfR) m b
(=<<) = flip (>>=)

(>=>) : Monad m => (a -> Ard board sfL m b) -> (b -> Ard board sfR m c) -> a -> Ard board (sfL >=> sfR) m c
(>=>) fl fr x = fl x >>= fr

(<=<) : Monad m => (b -> Ard board sfR m c) -> (a -> Ard board sfL m b) -> a -> Ard board (sfL >=> sfR) m c
(<=<) = flip (>=>)

infixl 1 *>>
||| Applicative-like `*>` operator but with lazy right argument
(*>>) : Monad m => Ard board sfL m a -> Lazy (Ard board sfR m b) -> Ard board (sfL >=> sfR) m b
l *>> r = l >>= \_ => r

----------------------
--- `Ard`'s runner ---
----------------------

-- Top-level (at the end of the day) runner for the `Ard`
runArd : (board : Board) -> {auto ev : IsJust $ sf InitialBoardState} -> Ard board sf m a -> m a
runArd _ (Wrapped act) = act
