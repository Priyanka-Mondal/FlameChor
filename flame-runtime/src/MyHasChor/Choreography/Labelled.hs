-- {-# LANGUAGE BlockArguments #-}
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
--{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}
-- {-# LANGUAGE BlockArguments #-}

module MyHasChor.Choreography.Labelled where

--import MyHasChor.Choreography
import MyHasChor.Choreography.Choreo
import Control.Concurrent.Async
import Control.Monad.Identity (Identity(..), runIdentity, void)
import MyHasChor.Choreography.Location
import Data.Proxy
--import Data.Time
import System.Environment
--import Control.Monad.Identity (Identity(..), runIdentity)
import "freer-simple" Control.Monad.Freer as S
--import "HasChor" Control.Monad.Freer (interpFreer, toFreer)
import MyHasChor.Control.Monad.Freer
import Flame.Principals
import Flame.TCB.Freer.IFC
    ( type (!)(..),
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
import MyHasChor.Choreography.Flaqr (HasFail(failVal))


-- labelIn :: (HasFail a) => l ! (a @ loc) -> (l!a) @ loc
-- labelIn lal = wrap $ bind lal ( \case
--                                     Wrap b -> label b
--                                     Empty ->  label failVal 
--                               )
instance Show a => Show (l ! a) where
  show (Seal x) = "Seal " ++ show x
instance Read a => Read (l ! a) where
  readsPrec _ s = [(Seal x, rest) | ("Seal", rest1) <- lex s, (x, rest) <- readsPrec 0 rest1]

labelIn :: l!(a @ loc) -> (l! a) @ loc
labelIn (Seal asl) = case asl of
                        Wrap as -> wrap $ Seal as
                        Empty   -> Empty                
                        
labelIn' :: (Monad m) => Labeled m pc (l!(a @ loc)) -> Labeled m pc ((l!a) @ loc)
labelIn' e = e >>= (\lal -> wrap <$> use lal (protect . unwrap))

-- | Interpret the effects in a freer monad in terms of another monad.
wrapLabeled :: forall pc m a loc. Monad m => Labeled m pc a -> Labeled m pc (a @ loc)
wrapLabeled = Prelude.fmap wrap --- ???

labelOut :: (l!a) @ loc -> l!(a @ loc) 
labelOut lal = bind (unwrap lal) (label . wrap) 

-- requires a locally ?? 
-- new unwrap version that labels and wraps Empty 

joinIn :: forall l l' l'' a loc. (Show a, Read a, l ⊑ l'', l' ⊑ l'') => l!((l'!a) @ loc) -> (l''!a) @ loc
joinIn = wrap . join . unwrap . labelIn

-- joinIn' :: forall l l' l'' pc m a loc. 
--   (Monad m, l ⊑ l'', l' ⊑ l'', Show a, Read a) => 
--   Labeled m pc (l ! ((l'!a) @ loc)) -> Labeled m pc ((l''!a) @ loc)
-- joinIn' lx = wrap <$> do 
--   x <- lx 
--   let x' = joinIn @l @l' @l'' x -- why didn't this get inferred?
--   use (unwrap x') protect

labelOut' :: forall loc m pc a l. (Monad m,  KnownSymbol loc, pc ⊑ l) => 
    Labeled (Choreo m) pc ((l!a) @ loc) -> Labeled (Choreo m) pc (l!(a @ loc))
labelOut' e = labelOut <$> e

joinOut :: forall l l' l'' a loc. (l ⊑ l'', l' ⊑ l'') => l!((l'!a) @ loc) -> l''!(a @ loc)
joinOut llal = bind llal (\lal -> bind (unwrap lal) $ label . wrap)

-- | Perform a local computation at a given location.
slocally :: forall pc loc_pc l loc m a. (Monad m, KnownSymbol loc, pc ⊑ loc_pc, pc ⊑ l,  Show a, Read a)
               => (SPrin pc, SPrin (N loc), SPrin loc_pc, SPrin l)
               -> (Unwrap loc -> Labeled m loc_pc (l!a))
               -> Labeled (Choreo m) pc ((l!a) @ loc) -- type changes
slocally (pc, loc, loc_pc, l) k = do
  result <- restrict pc (\_ -> locally (sym loc) $ (\un -> runLabeled $ k un))
  return $ labelIn (joinOut result) --labelIn

sPutStrLn  :: Show a => SPrin pc -> (l ⊑ pc) => l!a -> Labeled IO pc (pc!())
sPutStrLn  pc la = restrict pc (\open -> print $ open la)

sGetLine  :: SPrin pc -> Labeled IO pc (pc!String)
sGetLine  pc = restrict pc (\_ -> getLine)


sen :: forall a loc loc' pc l m. (Show a, Read a, KnownSymbol loc, KnownSymbol loc', Show (l!a), Read (l!a)) --, (N loc') ≽ (C pc), (N loc) ≽ (I pc))
     => (Proxy loc, SPrin pc, SPrin l, (l!a) @ loc)  
                                -- a sender's location, 
                                -- a clearance, 
                                -- and a value located at the sender
     -> Proxy loc'-- ^ A receiver's location.
     -> Labeled (Choreo m) pc ((pc!(l!a)) @ loc')
sen (loc, pc, l, la) loc' = do
  result <- restrict pc ( \_ -> (loc, la) ~> loc')
  return $ labelIn result