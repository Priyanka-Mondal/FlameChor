{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}

--{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}


module MyHasChor.Choreography.LabelledAsync where

--import MyHasChor.Choreography
import MyHasChor.Choreography.ChoreoAsync
import Control.Concurrent.Async
import Control.Monad.Identity (Identity(..), runIdentity, void)
import MyHasChor.Choreography.Location
import Control.Monad.IO.Class (liftIO)
import Data.Proxy
--import Data.Time
import System.Environment
--import Control.Monad.Identity (Identity(..), runIdentity)
import "freer-simple" Control.Monad.Freer as S
--import "HasChor" Control.Monad.Freer (interpFreer, toFreer)
import MyHasChor.Control.Monad.Freer

--import Control.Concurrent.Async (Async, wait)
import Control.Monad.IO.Class (MonadIO, liftIO)

import Flame.Principals
--import Flame.TCB.Freer.IFC (Seal (..))
import Flame.TCB.Freer.IFC
    ( type (!)(..),
      --Seal(..),
      Labeled,
      bind,
      label,
      use,
      protect,
      join,
      restrict,
      runLabeled,
      relabel' )
import Flame.Assert
import GHC.TypeLits (KnownSymbol)
import MyHasChor.Choreography.Network.Local (LocalConfig(locToBuf))
import MyHasChor.Choreography.Labelled
import MyHasChor.Choreography.Flaqr(compare)
import Flame.Runtime.Crypto.KeyMap (adjustKey)
import Data.Time.Format.ISO8601 (yearFormat)


labelInAsync :: l!(Async a @ loc) -> (l! Async a) @ loc
labelInAsync (Seal asl) = case asl of
                        Wrap as -> wrap $ Seal as
                        Empty   -> Empty


-- labelInIO :: l ! (Async a @ loc) -> (Async a -> a)  -> IO (Async (l!a)) @ loc
-- labelInIO lal f = wrap <$> async $ return $ bind lal (label . f . unwrap)

-- labelin :: l ! (Async a @ loc) -> (l! Async a) @ loc
-- labelin lal = wrap $ bind lal (label . unwrap)

-- labelI' :: (Monad m) => Labeled m pc (l!(a @ loc)) -> Labeled m pc ((l!a) @ loc)
-- labelI' e = e >>= (\lal -> wrap <$> use lal (protect . unwrap))

labelIn' :: (Monad m) => Labeled m pc (l!(Async a @ loc))-> 
    Labeled m pc ((l! Async a) @ loc)
labelIn' e = labelIn <$> e  --e >>= (\lal -> wrap <$> use lal (protect.unwrap))

-- | Interpret the effects in a freer monad in terms of another monad.
wrapLabeled :: forall pc m a loc. Monad m => Labeled m pc a -> Labeled m pc (a @ loc)
wrapLabeled = Prelude.fmap wrap --- ???

labelOutAsync :: forall l a loc. Async (l!a) @ loc -> l!(Async a @ loc)
labelOutAsync (Wrap as) = Seal (Wrap $ Prelude.fmap (\(Seal a) -> a) as)
labelOutAsync Empty     = Seal Empty

labeloutM :: Labeled m pc (Async (l!a) @ loc) -> Labeled m pc (l!(Async a @ loc))
labeloutM e = labelOutAsync <$> e

-- joinInAsync :: forall l l' l'' a loc. (Show a, Read a, l ⊑ l'', l' ⊑ l'') => 
--  l!((l'! Async a) @ loc) -> (l''!Async a) @ loc
-- joinInAsync lal = labelInAsync $ join $ bind lal (label . labelOutAsync) -- Using unwrap

-- joinInAsync' :: forall l l' l'' pc m a loc. 
--   (Monad m, l ⊑ l'', l' ⊑ l'', Show a, Read a) => 
--   Labeled m pc (l ! ((l'! Async a) @ loc)) -> Labeled m pc ((l''! Async a) @ loc)
-- joinInAsync' lx = joinInAsync <$> lx
 
labelOut' :: forall loc m pc a l. (Monad m,  KnownSymbol loc, pc ⊑ l) => 
    Labeled (Choreo m) pc ((l!a) @ loc) -> Labeled (Choreo m) pc (l!(a @ loc))
labelOut' e = labelOut <$> e

joinOutAsync :: forall l l' l'' a loc. (l ⊑ l'', l' ⊑ l'') => -- added l ⊑ l'
 l!(Async (l'! a) @ loc) -> l''!(Async a @ loc)
joinOutAsync lal = join $ bind lal (label . labelOutAsync)

-- joinOutAsync' :: forall l l' l'' a loc. (l ⊑ l'', l' ⊑ l'') => -- added l ⊑ l'
--  (l ! Async (l'! a)) @ loc -> l''!(Async a @ loc)
-- joinOutAsync' (Wrap as) = join $ bind as ()
-- --Seal (label $ Wrap $ Prelude.fmap (\(Seal a) -> a) as)
-- joinOutAsync' Empty     = Seal Empty

--joinOutAsync' lal = join $ bind lal (label . labelOutAsync)

sLocally :: forall pc loc_pc l loc m a. (Monad m, KnownSymbol loc, pc ⊑ loc_pc, pc ⊑ l,  Show a, Read a)
               => (SPrin pc, SPrin (N loc), SPrin loc_pc, SPrin l)
               -> (Unwrap loc -> Labeled m loc_pc (l!a))
               -> Labeled (Choreo m) pc ((l! a) @ loc) -- type changes
sLocally (pc, loc, loc_pc, l) k = do
  result <- restrict pc (\_ -> locally (sym loc) (\un -> runLabeled $ k un))
  return $ labelIn (joinOut result) --labelIn

sLocallyAsync :: forall pc loc_pc l loc m a. (Monad m, KnownSymbol loc, pc ⊑ loc_pc, pc ⊑ l,  Show a, Read a)
               => (SPrin pc, SPrin (N loc), SPrin loc_pc, SPrin l)
               -> (Unwrap loc -> Labeled m loc_pc (l! Async a))
               -> Labeled (Choreo m) pc (l! Async a @ loc) -- type changes
sLocallyAsync (pc, loc, loc_pc, l) k = do
  result <- restrict pc (\_ -> locally (sym loc) (\un -> runLabeled $ k un))
  return $ labelIn (joinOut result) --labelIn

labelInA :: l!(Async a @ loc) -> Async (l!a) @ loc
labelInA (Seal asl) = case asl of
                        Wrap as -> Wrap $ Prelude.fmap Seal as
                        Empty   -> Empty

(~>:) :: forall a loc loc' pc l m. (Show a, Read a, KnownSymbol loc, KnownSymbol loc', Show (l!a), Read (l!a)) --, (N loc') ≽ (C pc), (N loc) ≽ (I pc))
     => (Proxy loc, SPrin pc, SPrin l, (l!a) @ loc)  
     -> Proxy loc'
     -> Labeled (Choreo m) pc (Async (pc!(l!a)) @ loc')
(~>:) (loc, pc, l, la) loc' = do
  result <- restrict pc (\_ -> (loc, la) ~> loc')
  return $ labelInA result 

-- swait :: Async (l ! a) -> l ! Async a 
-- swait y = do
--   z <- wait y
--   bind z (\x -> label $ async x)
  

-- | Conditionally execute choreographies based on a located value.
sCond ::  forall pc l loc m a b. (Show a, Read a, KnownSymbol loc, pc ⊑ l)
     => (Proxy loc, SPrin pc, a @ loc) 
     -> (Async a -> Labeled (Choreo m) pc b) 
     -> Labeled (Choreo m) pc (l ! b)
sCond (l, pc, la) c = restrict pc $ \_ -> cond (l, la) (runLabeled . c)

sPutStrLn  :: Show a => SPrin pc -> (l ⊑ pc) => l!a -> Labeled IO pc (pc!())
sPutStrLn  pc la = restrict pc (\open -> print $ open la)

strGetLine  :: SPrin pc -> Labeled IO pc (pc ! Int)
strGetLine  pc = restrict pc (\_ -> readLn)

--(l ⊑ l') =>
--(l ! a) -> (a -> l' ! b) -> l' ! b

-- unwrapAsync :: Async (l ! a) -> l! (Async a)
-- unwrapAsync a = 


-- data LabeledAsync l a where
--   LAsync :: Async (l ! a) -> LabeledAsync l a

-- -- | Wait for the asynchronous computation to complete and return the result.
-- waitL :: MonadIO m => LabeledAsync l a -> m a
-- waitL (LAsync async) = liftIO $ wait async

-- -- | Create a labeled asynchronous computation from an 'Async' computation.
-- asyncL :: Async a -> LabeledAsync l a
-- asyncL = LAsync 

-- asyncWait :: forall a b l l' l'' loc. ((l ⊑ l'', l' ⊑ l'')) =>
--   Async (l ! a) @ loc -> (Async (l ! a) @ loc -> Async (l ! a)) 
--                                                   -> (l ! a)
-- asyncWait lal un = do 
--   let z = un lal
--   y <- (\_ -> wait z) 
--   return y

--   --return $ join y
  
  
-- --   bind (un lal) (\x -> do 
-- --             label $ bind (labelOutAsync (wrap x)) (\y -> do 
-- --                                                   z <- wait (un y)
-- --                                                   label z
-- --                                                  ))