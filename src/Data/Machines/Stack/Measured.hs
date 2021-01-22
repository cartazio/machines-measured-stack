{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types, ScopedTypeVariables, BangPatterns #-}
--- adapted from Data.Machine.Stack
module Data.Machines.Stack.Measured  ( Stack(..)
  , stack
  , peek
  , measure
  , pop
  , push
  ) where

import Data.Machine.Plan
import Data.Machine.Type
import Data.Semigroup

-- | This is a simple process type that knows how to push back input.
data Stack s a r where
  Push :: a -> Stack s a ()
  Pop  ::      Stack  s a a
  Measured ::  Stack s a s
-- | Peek at the next value in the input stream without consuming it
peek :: Plan (Stack s a) b a
peek = do
  a <- pop
  push a
  return a
{-# INLINABLE peek #-}

-- | Push back into the input stream
push :: a -> Plan (Stack s a) b ()
push a = awaits (Push a)
{-# INLINABLE push #-}

-- | Pop the next value in the input stream
pop :: Plan (Stack s a) b a
pop = awaits Pop
{-# INLINABLE pop #-}


measure :: Plan (Stack s a) b s
measure = awaits Measured

-- | Stream outputs from one 'Machine' into another with the possibility
-- of pushing inputs back.
stack :: forall m s k a o . (Monad m, Semigroup s) =>
        MachineT m k a -> MachineT m (Stack s a) o -> s  -> (a -> s ) -> (s -> s ) ->   MachineT m k o
stack  srcup srcdown  sinit measure neg  =
  let
    stackem :: MachineT m k a -> MachineT m (Stack s a) o  -> s -> MachineT m k o
    stackem up down !stat =
--- NB: stat should *maybe* be strict
      stepMachine down $ \stepD     ->
      case stepD of
        Stop                     -> stopped
        Yield o down'            -> encased (Yield o (up `stackem` down' $   stat ))
        Await down' (Push a) _   -> encased (Yield a up) `stackem` (down' ()) $    (stat <>  neg (measure a))
        Await down'  (Measured) _  ->  up `stackem` (down' stat)  $  stat
        Await down' Pop ffD      ->
          stepMachine up $ \stepU   ->
          case stepU of
            Stop                 -> stopped `stackem` ffD $  stat
            Yield o up'          -> up'     `stackem` down' o $ (stat <> measure o )
            Await up' req ffU    -> encased (Await (\a -> up' a `stackem` encased stepD  $ stat ) req
                                                   (      ffU   `stackem` encased stepD  $ stat ))
  in
    stackem srcup srcdown sinit
{-# INLINABLE stack #-}


