{-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
    DataKinds, RankNTypes, FlexibleInstances, FlexibleContexts, TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PackageImports #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fplugin Flame.Solver -fobject-code #-}

module Flame.TCB.Freer.IFC where

import Flame.Principals
import "HasChor" Control.Monad.Freer
    ( interpFreer, toFreer, Freer )
import "HasChor" Control.Monad.Freer
    ( interpFreer, toFreer, Freer )
import Data.Type.Bool
import Data.Proxy (Proxy(..))
import Data.Kind (Type)
import Data.Functor
import Data.Constraint
import Data.Constraint.Unsafe
import Data.Reflection
-- import Data.Singletons (Apply, TyFun)
import GHC.TypeLits (TypeError, ErrorMessage(..))
import System.IO
import Control.Monad ((>=>))
import Control.Monad.Identity


-- instance (Member (Labeled pc) r) => LabeledMember pc r where
data (l::KPrin) ! a  where
  Seal :: { unseal :: a }  -> l!a
  deriving (Show, Read) -- these instances should be explicitly
                        -- most likely, they should encrypt and decrypt

type Clearance pc = forall a l. (l ⊑ pc) => l!a -> a

-- type Use pc = forall pc a l. (l⊑pc) => (l ! a) -> a
data LabeledSig m (pc::KPrin) a where
    Restrict :: (Monad m, pc ⊑ l) => !(SPrin pc) -> (Clearance pc -> m a) -> LabeledSig m pc (l!a)
    Protect  :: (Monad m, pc ⊑ l) => a -> LabeledSig m pc (l!a)
    Use      :: (Monad m, l' ⊑ l, l' ⊑ pc') =>
      l'!b -> (b -> Labeled m pc' (l!a)) -> LabeledSig m pc (l!a)

type Labeled m pc = Freer (LabeledSig m pc)

restrict :: SPrin pc -> (Monad m, pc ⊑ l) => (Clearance pc -> m a) -> Labeled m pc (l!a)
restrict pc ma = toFreer (Restrict pc ma)

protect :: (Monad m, pc ⊑ l) => a -> Labeled m pc (l!a)
protect a = toFreer (Protect a)

use :: (Monad m, l' ⊑ l, l' ⊑ pc') => l'!b -> (b -> Labeled m pc' (l!a)) -> Labeled m pc (l!a)
use b k = toFreer (Use b k)

label :: forall l a. a -> l!a
label = runIdentity . runLabeled . protect

relabel :: forall l l' a. l ⊑ l' => l!a -> l'!a
relabel = runIdentity . runLabeled . \x -> use x protect

--- Is this secure? 
-- runLabeled $ join' $ restrict high $ \un -> 
--    if (un secret) then (runLabeled lowT) else (runLabeled lowF)
      
relabel' :: forall l l' pc pc' m a. (Monad m, l ⊑ l', pc ⊑ l') => 
              SPrin pc -> Labeled m pc' (l!a) -> Labeled m pc (l'!a)
relabel' pc e = join' $ restrict pc $ \_ -> do 
  x <- runLabeled e
  return $ relabel x
  
join :: forall l l' l'' a. (l ⊑ l'', l' ⊑ l'') => l!(l'!a) -> l''!a
join = runIdentity . runLabeled . \x -> use x (`use` protect)

join' :: forall l l' l'' pc m a. (Monad m, l ⊑ l'', l' ⊑ l'') => Labeled m pc (l!(l'!a)) -> Labeled m pc (l''!a)
join' lx = lx >>= (\x -> use x (`use` protect))

bind :: forall l l' a b. l ⊑ l' => l!a -> (a -> l'!b) -> l'!b
bind la k = runIdentity . runLabeled $ use la (join' @_ @l' @l' @l' . protect . k)

fmap :: (Monad m, l ⊑ l', pc ⊑ pc', l ⊑ pc', pc' ⊑ l') =>
    (a -> b) -> l!a -> l'!b
fmap f = runIdentity . runLabeled . (`use` (protect . f))

runLabeled :: forall pc m a. Monad m => Labeled m pc a -> m a
runLabeled = interpFreer handler
  where
    handler :: forall pc m a. Monad m => LabeledSig m pc a -> m a
    handler (Restrict pc ma) = ma unseal <&> Seal
    handler (Protect a) = pure (Seal a)
    handler (Use (Seal b) k)  = runLabeled $ k b

-- chooseSecret :: (l ⊑ pc, l' ⊑ pc) => 
--     SPrin pc -> SPrin l -> SPrin l' -> l!Bool -> l'!Int -> l'!Int -> Labeled IO pc (pc!())
-- chooseSecret pc l l' lb n1 n2 = use lb
--      (\b ->  if b then
--                  relabel' $ s_putStrLn n1 
--              else 
--                  relabel' $ s_putStrLn n2)
--    where 
--      s_putStrLn la = restrict pc (\un -> putStrLn (show (un la)))
--         
-- 
-- type Alice = KName "Alice"
-- alice :: SPrin Alice
-- alice = SName (Proxy :: Proxy "Alice")
-- type Bob = KName "Bob"
-- bob :: SPrin Bob
-- bob = SName (Proxy :: Proxy "Bob")
-- 
-- main :: IO (Alice!())
-- main = runLabeled $ chooseSecret alice alice bob (Seal True :: Alice!Bool) (Seal 1 :: Bob!Int) (Seal 2 :: Bob!Int)