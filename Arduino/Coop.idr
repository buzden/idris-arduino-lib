module Arduino.Coop

import public Arduino.Time
import Arduino.Util

import Data.List

import Control.Monad.Syntax
import Control.Monad.Trans

%default total

------------------
--- Interfaces ---
------------------

public export
interface Parallel (m : Type -> Type) where
  -- Alternative-like operator with parallel semantics and unavailable results of separate computations
  (<||>) : m Unit -> m Unit -> m Unit

------------
--- Data ---
------------

export
data Coop : (m : Type -> Type) -> (a : Type) -> Type where
  Point       : (1 _ : m a) -> Coop m a
  Sequential  : Coop m a -> (a -> Coop m b) -> Coop m b
  Cooperative : Coop m a -> Coop m b -> Coop m Unit
  DelayedTill : Time -> Coop m Unit
  DebugInfo   : String -> Coop m a -> Coop m a

--------------------------------
--- Basic creation functions ---
--------------------------------

export
atomic : (1 _ : m a) -> Coop m a
atomic = Point

export
debugInfo : String -> Coop m a -> Coop m a
debugInfo = DebugInfo

-----------------------
--- Implementations ---
-----------------------

export
Timed m => Timed (Coop m) where
  currentTime = debugInfo "returned curr time" $ Point currentTime

infixl 4 $>

($>) : Applicative m => Coop m a -> b -> Coop m b
(Point _)        $> b = debugInfo "point $>" . Point $ pure b
(Sequential a f) $> b = Sequential a $ \ar => f ar $> b
(DebugInfo msg c) $> b = debugInfo (msg ++ " {$>-ed}") $ c $> b
x                $> b = Sequential x . const . debugInfo "point abandon" . Point $ pure b

export
Applicative m => Functor (Coop m) where
  map f (Point a)           = debugInfo "map-point" $ Point (map f a)
  map f (Sequential a b)    = Sequential a $ \ar => map f $ b ar
  map f x@(Cooperative _ _) = x $> f ()
  map f x@(DelayedTill t)   = x $> f ()
  map f (DebugInfo msg c)   = debugInfo (msg ++ " {mapped}") $ map f c

export
Applicative m => Applicative (Coop m) where
  pure    = debugInfo "appl pure" . Point . pure
  l <*> r = Sequential l $ \lf => map lf r
  -- This could be `(<*>) = Cooperative apply`, but it must be consistent with `(>>=)` definition.
  -- Consider code `doSmth *> delayedFor 100 *> doMore` comparing to `(doSmth <||> delayedFor 100) *> doMore`.
  -- Having parallel semantics for the `Applicative`'s `<*>`, those two examples above will mean the same, which seems to be unexpected.

export
Monad m => Monad (Coop m) where
  (>>=) = Sequential

export
Parallel (Coop m) where
  (<||>) = Cooperative

export
Monad m => DelayableTill (Coop m) where
  delayTill = DelayedTill

export
(Timed m, Monad m) => DelayableFor (Coop m) where
  delayFor t = delayTill . (+t) =<< currentTime

export
HasIO (Coop IO) where
  liftIO = atomic

export
MonadTrans Coop where
  lift = atomic

-------------------
--- Interpreter ---
-------------------

Sync : Type
Sync = Nat

-- Two present fences with the same sync are meant to be blocking each other.
-- Postponed `Coop m y` needs to be sheduled only when all events with its sync are over.
-- `Sync` type is a comparable type and is a workaround of uncomparability of `Coop`.
data Fence : (Type -> Type) -> Type where
  No : Fence m
  Sy : Sync -> (postponed : Coop m y) -> (next : Fence m) -> Fence m

data Event : (Type -> Type) -> Type where
  Ev : (t : Time) -> Coop m x -> Fence m -> Event m

namespace DebugStuff

  public export
  interface Debug (m : Type -> Type) where
    debug : String -> m ()

  export
  Show (Coop m a) where
    show (Point ma) = "atomic"
    show (Sequential l c) = "(" ++ show l ++ " => " ++ "parameterized continuation)"
    show (Cooperative a b) = "(" ++ show a ++ ") || (" ++ show b ++ ")"
    show (DelayedTill t) = "delay till " ++ show t
    show (DebugInfo msg c) = show c ++ " {" ++ msg ++ "}"

  export
  Show (Fence m) where
    show No         = "nofence"
    show (Sy n _ _) = "sync " ++ show n

  export
  Show (Event m) where
    show (Ev t coop fence) = show t ++ " | " ++ show coop ++ " | " ++ show fence

-- The following comparison is only according to the time; this will incorrectly work for sets.
-- Equally timed events with different actions are considered to be equal with `==` relation.
[TimeOnly_EvEq] Eq (Event m) where
  (Ev tl _ _) == (Ev tr _ _) = tl == tr

[TimeOnly_EvOrd] Ord (Event m) using TimeOnly_EvEq where
  compare (Ev tl _ _) (Ev tr _ _) = tl `compare` tr

export covering
runCoop : (Monad m, Timed m, Debug m) => Coop m Unit -> m Unit
runCoop co = runLeftEvents [Ev !currentTime co No] where

  -- TODO to replace list with a sortedness-preserving kinda-list
  covering
  runLeftEvents : List $ Event m -> m Unit
  runLeftEvents [] = pure ()
  runLeftEvents evs@(currEv@(Ev currEvTime currCoop currFence)::restEvs) = do
    debug $ show evs
    nextEvs <- if !currentTime >= currEvTime
               then do
                 let newLeftEvs = merge @{TimeOnly_EvOrd} restEvs !(newEvsAfterRunningCurr currEv)
                 pure $ merge @{TimeOnly_EvOrd} newLeftEvs $ awakened newLeftEvs
               else
                 -- TODO else wait for the `currEvTime - !currentTime`; or support and perform permanent tasks
                 pure evs
    runLeftEvents nextEvs

  where
    syncs : List (Event m) -> List Sync
    syncs evs = evs >>= \(Ev _ _ fence) => syncsOfFence fence where
      syncsOfFence : Fence m -> List Sync
      syncsOfFence No          = []
      syncsOfFence (Sy s _ fe) = s :: syncsOfFence fe

    uniqueSync : Lazy Sync
    uniqueSync = case syncs evs of
      []         => 0
      ss@(t::ts) => case foldl min t ts of
        S x => x                  -- either minimal minus 1
        Z   => S $ foldl max 0 ss -- or maximal plus 1

    -- All actions of form `patterm => pure [Ev ..., ...]` can be thought as a rewriting rule upon the list of events.
    newEvsAfterRunningCurr : Event m -> m (List $ Event m)
    newEvsAfterRunningCurr (Ev currEvTime currCoop currFence) = case currCoop of
      Point x                        => x $> Nil
      Cooperative l r                => pure [Ev currEvTime l currFence, Ev currEvTime r currFence]
      DelayedTill d                  => pure [Ev d (debugInfo "delayed end" . Point $ pure ()) currFence] -- this enables currFence to be run when appropriate (delayed)
      Sequential (Point y)         f => map (\r => [Ev currEvTime (debugInfo "applied continuation" $ f r) currFence]) y
      Sequential (Sequential y g)  f => pure [Ev currEvTime (debugInfo "postponed seq" $ Sequential y $ debugInfo "postponed tail" . g >=> f) currFence]
      Sequential (DelayedTill d)   f => pure [Ev d (debugInfo "delayed seq" $ f ()) currFence]
      Sequential (Cooperative l r) f => let newFence = Sy (Force uniqueSync) (f ()) currFence in -- coop in the `currFence` needs to be run after the `f ()`
                                        pure [Ev currEvTime l newFence, Ev currEvTime r newFence]
      DebugInfo _ c                  => newEvsAfterRunningCurr $ Ev currEvTime c currFence
      Sequential (DebugInfo _ c)   f => newEvsAfterRunningCurr $ Ev currEvTime (Sequential c f) currFence

    awakened : (evsAfterCurr : List $ Event m) -> List $ Event m
    awakened evsAfterCurr = case currFence of
      No                    => []
      Sy sync coop subFence => if sync `elem` syncs evsAfterCurr
                                   then []                            -- then someone else will raise this
                                   else [Ev currEvTime coop subFence] -- no one that blocks is left
