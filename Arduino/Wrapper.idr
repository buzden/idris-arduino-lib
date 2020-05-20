module Arduino.Wrapper

import Arduino.Boards
import Arduino.Util

import Control.Monad.Syntax

%default total

----------------------------------------------
----------------------------------------------
---  Compile-time board state description  ---
----------------------------------------------
----------------------------------------------

public export
FactsList : Type
FactsList = List (obj : Type ** x : obj ** fact : (obj -> Type) ** fact x) -- omnityped list of facts

-- TODO To think of *list of lists of facts* instead of just a *list of facts*.
--      This is to give an ability to add two facts at once ("atomically")
--      without any need to check parallel computation on each separate added fact.
--
--      However, already passed facts can still be hold flattened.

-- Returns `Nothing` when not possible
public export
CombineFactsLists : (before : FactsList) -> (after1, after2 : FactsList) -> Maybe FactsList
CombineFactsLists = ?combineFactsLists_rhs

------------------------------------------------------------------------
------------------------------------------------------------------------
---  Data structure embedding effect and its type-level description  ---
------------------------------------------------------------------------
------------------------------------------------------------------------

export
data Ard : (board : Board)
        -> (stateFun : FactsList -> Maybe FactsList) -- `Nothing` when board's state is not acceptable
        -> (m : Type -> Type) -> Type -> Type where
  Wrapped : m a -> Ard board stateFun m a

export
ard : m a -> Ard board stateFun m a
ard = Wrapped

-------------------------
--- Functor for `Ard` ---
-------------------------

export
Functor m => Functor (Ard board stateFun m) where
  map f (Wrapped act) = Wrapped $ map f act

--------------------------------------------
--- Applicative-like functions for `Ard` ---
--------------------------------------------

export
pure : Applicative m => a -> Ard board Prelude.Applicative.pure m a
pure = Wrapped . pure

export
(<*>) : Applicative m => Ard board sfL m (a -> b) -> Ard board sfR m a -> Ard board (sfL >=> sfR) m b
(Wrapped f) <*> (Wrapped x) = Wrapped $ f <*> x

--- Additional applicative-like syntax ---

export
(*>) : Applicative m => Ard board sfL m a -> Ard board sfR m b -> Ard board (sfL >=> sfR) m b
(Wrapped l) *> (Wrapped r) = Wrapped $ l *> r

export
(<*) : Applicative m => Ard board sfL m a -> Ard board sfR m b -> Ard board (sfL >=> sfR) m a
(Wrapped l) <* (Wrapped r) = Wrapped $ l <* r

--------------------------------------------
--- Alternative-like functions for `Ard` ---
--------------------------------------------

-- TODO to think whether `Applicative.pure` is a correct state change parameter for the `empty` action.
export
empty : Alternative m => Ard board Prelude.Applicative.pure m a
empty = Wrapped $ empty

-- The following function is a workarond of a compiler bug, which you run into when inline it.
public export -- because it is used in the type signature of `export`'ed `(<|>)`
CombineMaybeFactsLists : FactsList -> Maybe FactsList -> Maybe FactsList -> Maybe FactsList
CombineMaybeFactsLists original ml mr = CombineFactsLists original !ml !mr

export
(<|>) : Alternative m => Ard board sfL m a
                      -> Ard board sfR m a
                      -> Ard board (\st => CombineMaybeFactsLists st (sfL st) (sfR st)) m a
(Wrapped l) <|> (Wrapped r) = Wrapped $ l <|> r

--------------------------------------
--- Monad-like functions for `Ard` ---
--------------------------------------

export
(>>=) : Monad m => Ard board sfL m a -> (a -> Ard board sfR m b) -> Ard board (sfL >=> sfR) m b
(Wrapped l) >>= f = Wrapped $ l >>= \x => let Wrapped r = f x in r

export
join : Monad m => Ard board sfL m (Ard board sfR m a) -> Ard board (sfL >=> sfR) m a
join (Wrapped l) = Wrapped $ l >>= \ard => let Wrapped r = ard in r

--- Additional monad-like syntax ---

export
(=<<) : Monad m => (a -> Ard board sfR m b) -> Ard board sfL m a -> Ard board (sfL >=> sfR) m b
(=<<) = flip (>>=)

export
(>=>) : Monad m => (a -> Ard board sfL m b) -> (b -> Ard board sfR m c) -> a -> Ard board (sfL >=> sfR) m c
(>=>) fl fr x = fl x >>= fr

export
(<=<) : Monad m => (b -> Ard board sfR m c) -> (a -> Ard board sfL m b) -> a -> Ard board (sfL >=> sfR) m c
(<=<) = flip (>=>)

infixl 1 *>>
||| Applicative-like `*>` operator but with lazy right argument
export
(*>>) : Monad m => Ard board sfL m a -> Lazy (Ard board sfR m b) -> Ard board (sfL >=> sfR) m b
l *>> r = l >>= \_ => r

----------------------
--- `Ard`'s runner ---
----------------------

-- Top-level (at the end of the day) runner for the `Ard`
export
runArd : (board : Board) -> {auto ev : IsJust $ sf Prelude.Applicative.empty} -> Ard board sf m a -> m a
runArd _ (Wrapped act) = act
