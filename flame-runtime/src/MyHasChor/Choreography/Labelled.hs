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


module MyHasChor.Choreography.Labelled where


import MyHasChor.Choreography
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
    ( type (!),
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




labelIn :: l ! (a @ loc) -> (l!a) @ loc
labelIn lal = wrap $ bind lal (label . unwrap)

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


labelOut' :: forall loc m pc a l. (Monad m,  KnownSymbol loc, pc ⊑ l) => 
    Labeled (Choreo m) pc ((l!a) @ loc) -> Labeled (Choreo m) pc (l!(a @ loc))
labelOut' e = labelOut <$> e
-- labelOut' e = e >>= (\lal -> use (unwrap lal) (protect . wrap))
   
  
  -- unwrap inside `locally`, so that we have either the l!a or Empty
  -- but if its Empty how can we execute "use" on the value 
    
  --restrict pc (\_ -> locally loc (\un -> un x))
  --restrict pc (\_ -> loc `locally` \un ->  un x)
  -- use (\_ -> loc `locally` \un ->  un x) (protect. wrap)
  --protect $ loc `locally` \_ -> e >>= (\lal -> use (unwrap lal) (wrap))
--(Unwrap loc -> Labeled m loc_pc (l!a))



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
