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
Fact = ((objType : Type ** objType), (factType : Type ** factType))

infix 6 `withFact`
infixl 5 `Then`, `Then1`

public export
withFact : (obj : objType) -> (fact : factType) -> Fact
withFact obj fact = ((_ ** obj), (_ ** fact))

-- Specialized list is used to make used to not be able to append the wrong side and similar things.
public export
data FactsList : Type where
  NoFacts : FactsList
  Then1   : FactsList -> Fact -> FactsList

-- TODO To think of adding `ThenAtomic : FactsList -> List Fact -> FactsList` or similar constructor.
--      This is to give an ability to add two facts at once ("atomically")
--      without any need to check parallel computation on each separate added fact.

--- Building ---

public export
oneFact : (obj : objType) -> (fact : factType) -> FactsList
oneFact = Then1 NoFacts .. withFact

public export
Then : FactsList -> FactsList -> FactsList
Then fs NoFacts        = fs
Then fs (ss `Then1` x) = (fs `Then` ss) `Then1` x

||| Type-level conjunction of two preconditions with a modification of input between.
public export
ConseqConj : (FactsList -> Type) -> FactsList -> (FactsList -> Type) -> FactsList -> Type
ConseqConj preL afterL preR fs = (preL fs, preR $ fs `Then` afterL)

--- Querying ---

public export
data LastFactEq : (obj : objType) -> (expectedFact : factType) -> FactsList -> Type where
  LastMatches : (facts : FactsList)
             -> (obj : objType)
             -> (fact : factType)
             -> LastFactEq obj fact $ facts `Then1` obj `withFact` fact
  AnotherFactType : {fact : factType}
                 -> LastFactEq obj fact facts
                 -> (another : anotherFactType)
                 -> Uninhabited (factType = anotherFactType)
                 => LastFactEq obj fact $ facts `Then1` obj `withFact` another
  AnotherObj : {obj : objType}
            -> LastFactEq obj ft facts
            -> (anotherObj : objType)
            -> Uninhabited (obj = anotherObj)
            => LastFactEq obj ft $ facts `Then1` anotherObj `withFact` someFact
  AnotherObjType : {obj : objType}
                -> LastFactEq obj ft facts
                -> (anotherObj : anotherObjType)
                -> Uninhabited (objType = anotherObjType)
                => LastFactEq obj ft $ facts `Then1` anotherObj `withFact` someFact

  -- Well, `AnotherObj` and `AnotherObjType` can be joined, but I'm afraid of applying `=` to stuff with different types?

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
  Nil  : {auto ev : cond facts} -> WithAllAdditions cond facts NoFacts
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
