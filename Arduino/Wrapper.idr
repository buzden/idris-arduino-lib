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

-- TODO To think of `Then1` constructor that actually adds only when added stuff differs from the last known for the given object and fact type.
--      Think of forever spinning: this shouldn't add infinite amount of new facts if only one fact happens constantly.

--- Building ---

public export
oneFact : (obj : objType) -> (fact : factType) -> FactsList
oneFact = Then1 NoFacts .. withFact

public export
Then : FactsList -> FactsList -> FactsList
Then fs NoFacts        = fs
Then fs (ss `Then1` x) = (fs `Then` ss) `Then1` x

public export
data IsContainedIn : (what : Type) -> (wh : Type) -> Type where
  Base    : x `IsContainedIn` x
  AddTop  : x `IsContainedIn` (rest, x)
  AddDeep : x `IsContainedIn` outer -> x `IsContainedIn` (outer, y)

public export
data IsTypeConj : (l : Type) -> (r : Type) -> (res : Type) -> Type where
  LeftId         : IsTypeConj Unit r    r
  RighId         : IsTypeConj l    Unit l
  LeftZero       : IsTypeConj Void r    Void
  RightZero      : IsTypeConj l    Void Void
  LeftEqual      : {auto eq : l = r} -> IsTypeConj l r l
  RightEqual     : {auto eq : l = r} -> IsTypeConj l r r
  LeftContained  : {auto ev : r `IsContainedIn` l} -> IsTypeConj l r l
  RightContained : {auto ev : l `IsContainedIn` r} -> IsTypeConj l r r
--  Both           : IsTypeConj l r (l, r)

public export
TypeConj : (l : Type) -> (r : Type) -> {auto itc : IsTypeConj l r res} -> Type
TypeConj {res} _ _ = res

public export
data IsConseqConj : (FactsList -> Type) -> FactsList -> (FactsList -> Type) -> (res : FactsList -> Type) -> Type where
  MkConseqConj : {auto itc : IsTypeConj (preL fs) (preR $ fs `Then` afterL) (res fs)} -> IsConseqConj preL afterL preR res

-- TODO To make the "conjunction" above to have a single canonical form, e.g. to have `Conseq p NoFact p` be actually equal to `p` itself.
--      This is important e.g. for having non-hacking way for implementing `forever`.

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
(<*>) : Applicative m => Ard board preL afL m (a -> b) -> Ard board preR afL m a
     -> {auto icj : IsConseqConj preL afL preR conj} -> Ard board conj (afL `Then` afR) m b
(Wrapped f) <*> (Wrapped x) = Wrapped $ f <*> x

--- Additional applicative-like syntax ---

export
(*>) : Applicative m => Ard board preL afL m a -> Ard board preR afR m b
    -> {auto icj : IsConseqConj preL afL preR conj} -> Ard board conj (afL `Then` afR) m b
(Wrapped l) *> (Wrapped r) = Wrapped $ l *> r

export
(<*) : Applicative m => Ard board preL afL m a -> Ard board preR afR m b
    -> {auto icj : IsConseqConj preL afL preR conj} -> Ard board conj (afL `Then` afR) m a
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
(>>=) : Monad m => Ard board preL afL m a -> (a -> Ard board preR afR m b)
     -> {auto icj : IsConseqConj preL afL preR conj} -> Ard board conj (afL `Then` afR) m b
(Wrapped l) >>= f = Wrapped $ l >>= \x => let Wrapped r = f x in r

export
join : Monad m => Ard board preL afL m (Ard board preR afR m a)
    -> {auto icj : IsConseqConj preL afL preR conj} -> Ard board conj (afL `Then` afR) m a
join (Wrapped l) = Wrapped $ l >>= \ard => let Wrapped r = ard in r

export covering
forever : Monad m => Ard board pre NoFacts m a -> Ard board pre NoFacts m b
forever (Wrapped x) = Wrapped foreverX
  where foreverX = x >>= \_ => foreverX

--- Additional monad-like syntax ---

export
(=<<) : Monad m => (a -> Ard board preR afR m b) -> Ard board preL afL m a
     -> {auto icj : IsConseqConj preL afL preR conj} -> Ard board conj (afL `Then` afR) m b
(=<<) = flip (>>=)

export
(>=>) : Monad m => (a -> Ard board preL afL m b) -> (b -> Ard board preR afR m c) -> a
     -> {auto icj : IsConseqConj preL afL preR conj} -> Ard board conj (afL `Then` afR) m c
(>=>) fl fr x = fl x >>= fr

export
(<=<) : Monad m => (b -> Ard board preR afR m c) -> (a -> Ard board preL afL m b) -> a
     -> {auto icj : IsConseqConj preL afL preR conj} -> Ard board conj (afL `Then` afR) m c
(<=<) = flip (>=>)

infixl 1 *>>
||| Applicative-like `*>` operator but with lazy right argument
export
(*>>) : Monad m => Ard board preL afL m a -> Lazy (Ard board preR afR m b)
     -> {auto icj : IsConseqConj preL afL preR conj} -> Ard board conj (afL `Then` afR) m b
l *>> r = l >>= \_ => r

----------------------
--- `Ard`'s runner ---
----------------------

-- Top-level (at the end of the day) runner for the `Ard`
export
runArd : (board : Board) -> Ard board precond af m a -> {auto prf : precond NoFacts} -> m a
runArd _ (Wrapped act) = act

-- TODO `board` argument should be compile-time only, i.e. have quantity of `0`.
