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
{-# LANGUAGE ExplicitNamespaces #-}
--{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}


module MyHasChor.Choreography.LabelledAsync where

--import MyHasChor.Choreography
import MyHasChor.Choreography.ChoreoAsync
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
--labelIn :: l ! (a @ loc) -> (l!a) @ loc
--labelIn lal = wrap $ bind lal (label . unwrap)

--Async a -> Async (l!a)  -- functor
-- async (y <- wait (a)) 
-- fmap 

labelInAsync :: l!(Async a @ loc) -> (l! Async a) @ loc
labelInAsync (Seal asl) = case asl of
                        Wrap as -> wrap $ Seal as
                        Empty   -> Empty

labelInIO :: l ! (Async a @ loc) -> (Async a -> a)  -> IO (Async (l!a)) @ loc
labelInIO lal f = wrap <$> async $ return $ bind lal (label . f . unwrap)

labelin :: l ! (Async a @ loc) -> (l! Async a) @ loc
labelin lal = wrap $ bind lal (label . unwrap)

labelI' :: (Monad m) => Labeled m pc (l!(a @ loc)) -> Labeled m pc ((l!a) @ loc)
labelI' e = e >>= (\lal -> wrap <$> use lal (protect . unwrap))

labelIn' :: (Monad m) => Labeled m pc (l!(Async a @ loc))-> 
    Labeled m pc ((l! Async a) @ loc)
labelIn' e = e >>= (\lal -> wrap <$> use lal (protect.unwrap))

-- | Interpret the effects in a freer monad in terms of another monad.
wrapLabeled :: forall pc m a loc. Monad m => Labeled m pc a -> Labeled m pc (a @ loc)
wrapLabeled = Prelude.fmap wrap --- ???

labelOutAsync :: Async (l!a) @ loc -> l!(Async a @ loc)
labelOutAsync (Wrap as) = Seal (Wrap $ Prelude.fmap (\(Seal a) -> a) as)
labelOutAsync Empty     = Seal Empty

labeloutM :: Labeled m pc (Async (l!a) @ loc) -> Labeled m pc (l!(Async a @ loc))
labeloutM e = labelOutAsync <$> e

joinInAsync :: forall l l' l'' a loc. (Show a, Read a, l ⊑ l'', l' ⊑ l'') => 
 l!((l'! Async a) @ loc) -> (l''!Async a) @ loc
joinInAsync = wrap . join . unwrap . labelIn

joinInAsync' :: forall l l' l'' pc m a loc. 
  (Monad m, l ⊑ l'', l' ⊑ l'', Show a, Read a) => 
  Labeled m pc (l ! ((l'! Async a) @ loc)) -> Labeled m pc ((l''! Async a) @ loc)
joinInAsync' lx = joinInAsync <$> lx
  -- wrap <$> do 
  -- x <- lx 
  -- let x' = joinInAsync @_ @_ @_ x -- why didn't this get inferred?
  -- use (unwrap x') protect

labelOut' :: forall loc m pc a l. (Monad m,  KnownSymbol loc, pc ⊑ l) => 
    Labeled (Choreo m) pc ((l!a) @ loc) -> Labeled (Choreo m) pc (l!(a @ loc))
labelOut' e = labelOut <$> e

joinOutAsync :: forall l l' l'' a loc. (l ⊑ l'', l' ⊑ l'') => -- added l ⊑ l'
 l!(Async (l'! a) @ loc) -> l''!(Async a @ loc)
joinOutAsync lal = join $ bind lal (label . labelOutAsync)


sLocallyAsync :: forall pc loc_pc l loc m a. (Monad m, KnownSymbol loc, pc ⊑ loc_pc, pc ⊑ l,  Show a, Read a)
               => (SPrin pc, SPrin (N loc), SPrin loc_pc, SPrin l)
               -> (Unwrap loc -> Labeled m loc_pc (Async (l!a)))
               -> Labeled (Choreo m) pc ((l! Async a) @ loc) -- type changes
sLocallyAsync (pc, loc, loc_pc, l) k = do
  result <- restrict pc (\_ -> locally (sym loc) $ (\un -> runLabeled $ k un))
  return $ labelIn (joinOutAsync result) --labelIn

(~>:) :: forall a loc loc' pc l m. (Show a, Read a, KnownSymbol loc, KnownSymbol loc')--, Show (l!a), Read (l!a)) --, (N loc') ≽ (C pc), (N loc) ≽ (I pc))
     => (Proxy loc, SPrin pc, SPrin l, Async (l!a) @ loc)  
                                -- a sender's location, 
                                -- a clearance, 
                                -- and a value located at the sender
     -> Proxy loc'-- ^ A receiver's location.
     -> Labeled (Choreo m) pc ((pc!(l! Async a)) @ loc')
(~>:) (loc, pc, l, la) loc' = do
  result <- restrict pc ( \_ -> (loc, la) ~> loc')
  return $ labelIn result

-- | Conditionally execute choreographies based on a located value.
sCond ::  forall pc l loc m a b. (Show a, Read a, KnownSymbol loc, pc ⊑ l)
     => (Proxy loc, SPrin pc, a @ loc) -- ^ A pair of a location and a scrutinee located on
                                         -- it.
     -> (a -> Labeled (Choreo m) pc b) -- ^ A function that describes the follow-up
                          -- choreographies based on the value of scrutinee.
     -> Labeled (Choreo m) pc (l ! b)
sCond (l, pc, la) c = restrict pc $ \_ -> cond (l, la) (runLabeled . c)--(\la -> runLabeled $ c la)


sPutStrLn  :: Show a => SPrin pc -> (l ⊑ pc) => l!a -> Labeled IO pc (pc!())
sPutStrLn  pc la = restrict pc (\open -> print $ open la)

sGetLine  :: SPrin pc -> Labeled IO pc (pc!String)
sGetLine  pc = restrict pc (\_ -> getLine)
