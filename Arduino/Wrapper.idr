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
Fact : Type
Fact = (obj : Type ** x : obj ** fact : (obj -> Type) ** fact x)

public export
FactsList : Type
FactsList = List Fact -- omnityped list of facts

-- TODO To replace `List Fact` with a special type having `NoFacts` and `Then1` as a constructors.

-- TODO To think of *list of lists of facts* instead of just a *list of facts*.
--      This is to give an ability to add two facts at once ("atomically")
--      without any need to check parallel computation on each separate added fact.
--
--      However, already passed facts can still be hold flattened.

public export
NoFacts : FactsList
NoFacts = empty

--- Sequencing ---

infixl 6 `Then`, `Then1`

public export
Then : FactsList -> FactsList -> FactsList
Then = flip (++)

public export
Then1 : FactsList -> Fact -> FactsList
Then1 = flip (::)

||| Type-level conjunction of two preconditions with a modification of input between.
public export
ConseqConj : (FactsList -> Type) -> FactsList -> (FactsList -> Type) -> FactsList -> Type
ConseqConj preL afterL preR fs = (preL fs, preR $ fs `Then` afterL)

------------------------------------------------------------------------
------------------------------------------------------------------------
---  Data structure embedding effect and its type-level description  ---
------------------------------------------------------------------------
------------------------------------------------------------------------

export
data Ard : (board : Board)
        -> (precond : FactsList -> Type)
        -> (afterFacts : FactsList)
        -> (m : Type -> Type) -> Type -> Type where
  Wrapped : m a -> Ard board precond afterFacts m a

export
ard : m a -> Ard board precond afterFacts m a
ard = Wrapped

-------------------------
--- Functor for `Ard` ---
-------------------------

export
Functor m => Functor (Ard board precond afterFacts m) where
  map f (Wrapped act) = Wrapped $ map f act

--------------------------------------------
--- Applicative-like functions for `Ard` ---
--------------------------------------------

export
pure : Applicative m => a -> Ard board (const Unit) NoFacts m a
pure = Wrapped . pure

export
(<*>) : Applicative m => Ard board preL afL m (a -> b) -> Ard board preR afL m a -> Ard board (ConseqConj preL afL preR) (afL `Then` afR) m b
(Wrapped f) <*> (Wrapped x) = Wrapped $ f <*> x

--- Additional applicative-like syntax ---

export
(*>) : Applicative m => Ard board preL afL m a -> Ard board preR afR m b -> Ard board (ConseqConj preL afL preR) (afL `Then` afR) m b
(Wrapped l) *> (Wrapped r) = Wrapped $ l *> r

export
(<*) : Applicative m => Ard board preL afL m a -> Ard board preR afR m b -> Ard board (ConseqConj preL afL preR) (afL `Then` afR) m a
(Wrapped l) <* (Wrapped r) = Wrapped $ l <* r

--------------------------------------------
--- Alternative-like functions for `Ard` ---
--------------------------------------------

export
empty : Alternative m => Ard board (const Unit) NoFacts m a
empty = Wrapped empty

||| Means that given condition is true on given `facts` prepended with all prefixes (incl. empty) of `addition` list.
public export
data WithAllAdditions : (cond : FactsList -> Type) -> (facts : FactsList) -> (addition : FactsList) -> Type where
  Nil  : {auto ev : cond facts} -> WithAllAdditions cond facts []
  (::) : (fact : Fact) -> {auto ev : cond $ facts `Then` addition `Then1` fact} -> WithAllAdditions cond facts addition -> WithAllAdditions cond facts (addition `Then1` fact)

-- TODO to replace those above with a check on a full interleaving of after-fact prefixes.

export
(<|>) : Alternative m => Ard board preL afL m a
                      -> Ard board preR afR m a
                      -> Ard board (\fs => (WithAllAdditions preL fs afR, WithAllAdditions preR fs afL)) (afL `Then` afR) m a
(Wrapped l) <|> (Wrapped r) = Wrapped $ l <|> r

-- TODO to think whether sequential composition of facts (i.e., ``afL `Then` afR``) is enough for the resulting after-facts of parallel composition.

--------------------------------------
--- Monad-like functions for `Ard` ---
--------------------------------------

export
(>>=) : Monad m => Ard board preL afL m a -> (a -> Ard board preR afR m b) -> Ard board (ConseqConj preL afL preR) (afL `Then` afR) m b
(Wrapped l) >>= f = Wrapped $ l >>= \x => let Wrapped r = f x in r

export
join : Monad m => Ard board preL afL m (Ard board preR afR m a) -> Ard board (ConseqConj preL afL preR) (afL `Then` afR) m a
join (Wrapped l) = Wrapped $ l >>= \ard => let Wrapped r = ard in r

--- Additional monad-like syntax ---

export
(=<<) : Monad m => (a -> Ard board preR afR m b) -> Ard board preL afL m a -> Ard board (ConseqConj preL afL preR) (afL `Then` afR) m b
(=<<) = flip (>>=)

export
(>=>) : Monad m => (a -> Ard board preL afL m b) -> (b -> Ard board preR afR m c) -> a -> Ard board (ConseqConj preL afL preR) (afL `Then` afR) m c
(>=>) fl fr x = fl x >>= fr

export
(<=<) : Monad m => (b -> Ard board preR afR m c) -> (a -> Ard board preL afL m b) -> a -> Ard board (ConseqConj preL afL preR) (afL `Then` afR) m c
(<=<) = flip (>=>)

infixl 1 *>>
||| Applicative-like `*>` operator but with lazy right argument
export
(*>>) : Monad m => Ard board preL afL m a -> Lazy (Ard board preR afR m b) -> Ard board (ConseqConj preL afL preR) (afL `Then` afR) m b
l *>> r = l >>= \_ => r

----------------------
--- `Ard`'s runner ---
----------------------

-- Top-level (at the end of the day) runner for the `Ard`
export
runArd : (board : Board) -> Ard board precond af m a -> {auto prf : precond NoFacts} -> m a
runArd _ (Wrapped act) = act

-- TODO `board` argument should be compile-time only, i.e. have quantity of `0`.
