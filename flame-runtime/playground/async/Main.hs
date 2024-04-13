{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeOperators  #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}
{- HLINT ignore "Use <$>" -}
module Main where

import Choreography.NetworkAsync
import Choreography.NetworkAsync.Http
import Choreography.ChoreoAsync
import Control.Concurrent.Async
import System.Environment
import Data.Proxy
import Control.Monad.Identity (Identity(..), runIdentity, void)
import "freer-simple" Control.Monad.Freer as S
import "HasChor" Control.Monad.Freer (interpFreer, toFreer)
import Choreography.Location
import Data.Time
import GHC.TypeLits
import "HasChor" Choreography.ChoreoAsync

import Flame.Principals
import Flame.TCB.Freer.IFC
import Flame.Assert
import Control.Concurrent.Async (waitAny)

----------------------------------------------------------------------
-- Test asynchronous network programs
type A = N "A"
a :: SPrin A
a = SName (Proxy :: Proxy "A")

type B = N "B"
b :: SPrin B
b = SName (Proxy :: Proxy "B")

type CC = N "C"
c :: SPrin CC
c = SName (Proxy :: Proxy "C")

type D = N "D"
d :: SPrin D
d = SName (Proxy :: Proxy "D")

type AB = (A \/ B)
type AD = (A \/ D)
type ABD = ((AB) \/D)
type BD = (B \/ D)
type CD = (CC \/ D)

ab :: SPrin AB
ab = (a *\/ b )

ad :: SPrin AD
ad = (a *\/ d)

abd :: SPrin ABD
abd = ((a *\/ b ) *\/d)

type FromBuyer = ABD
fromBuyer :: SPrin ABD
fromBuyer = abd

type FromSeller = ABD
fromSeller :: SPrin ABD
fromSeller = abd

----------------------------------------------------------------------
-- Test asynchronous choreographies

locA :: Proxy "A"
locA = Proxy

locB :: Proxy "B"
locB = Proxy

locC :: Proxy "C"
locC = Proxy

locD :: Proxy "D"
locD = Proxy

labelIn :: l!(a @ loc) -> (l!a) @ loc
labelIn lal = wrap $ bind lal (label . unwrap)

labelIn' :: Monad m => Labeled m pc (l!(a @ loc)) -> Labeled m pc ((l!a) @ loc)
labelIn' e = e >>= (\lal -> wrap <$> (use lal (protect . unwrap)))

-- | Interpret the effects in a freer monad in terms of another monad.
wrapLabeled :: forall pc m a loc. Monad m => Labeled m pc a -> Labeled m pc (a @ loc)
wrapLabeled = Prelude.fmap wrap

labelOut :: (l!a) @ loc -> l!(a @ loc) 
labelOut lal = bind (unwrap lal) (label . wrap)

--asyncOut :: (l! (Async a)) @ loc -> (Async (l! a)) @ loc --l!(a @ loc) 
--asyncOut lal = bind (unwrap lal) (label . wrap)

labelOut' :: (Monad m, l ⊑ l'', l' ⊑ l'') => Labeled m pc ((l!a) @ loc) -> Labeled m pc (l!(a @ loc))
labelOut' e = e >>= (\lal -> (use (unwrap lal) (protect . wrap)))

joinIn :: forall l l' l'' a loc. (l ⊑ l'', l' ⊑ l'') => l!((l'!a) @ loc) -> (l''!a) @ loc
joinIn = wrap . join . unwrap . labelIn

--joinIn' :: forall l l' l'' pc m a loc. 
--  (Monad m, l ⊑ l'', l' ⊑ l'') => Labeled m pc (l!((l'!a) @ loc)) -> Labeled m pc ((l''!a) @ loc)
--joinIn' lx = wrap <$> do 
--  x <- lx 
--  let x' = (joinIn @l @l' @l'' x) -- why didn't this get inferred?
--  use (unwrap x') protect

joinOut :: forall l l' l'' a loc. (l ⊑ l'', l' ⊑ l'') => l!((l'!a) @ loc) -> l''!(a @ loc)
joinOut llal = bind llal (\lal -> bind (unwrap lal) $ label . wrap)

--asyncOut :: forall l a loc. (KnownSymbol loc) => (l!((Async a) @ loc)) -> Async (l!(a @ loc)) 
--asyncOut llal = bind llal (\lal -> bind (unwrap lal) $ label . wrap)

-- | Perform a local computation at a given location.
slocally :: forall pc loc_pc l loc m a. (Monad m, KnownSymbol loc, pc ⊑ loc_pc, pc ⊑ l)
               => (SPrin pc, SPrin (N loc), SPrin loc_pc, SPrin l)
               -> (Unwrap loc -> Labeled m loc_pc (l!a))
               -> Labeled (Choreo m) pc ((l!a) @ loc)
slocally (pc, loc, loc_pc, l) k = do
  result <- restrict pc (\_ -> locally (sym loc) $ (\un -> runLabeled $ k un))
  return $ labelIn (joinOut result)

(~>:) :: (Show a, Read a, KnownSymbol loc, KnownSymbol loc') --, (N loc') ≽ (C pc), (N loc) ≽ (I pc))
     => (Proxy loc, SPrin pc, SPrin l, (l!a) @ loc)  -- ^ A triple of a sender's location, 
                                            --a clearance, 
                                           -- and a value located
                                           -- at the sender
     -> Proxy loc'                           -- ^ A receiver's location.
     -> Labeled (Choreo m) pc ((pc!(Async(l!a))) @ loc')
     -- -> Labeled (Choreo m) pc ((pc!(l!a)) @ loc')
(~>:) (loc, pc, l, la) loc' = do
  result <-  restrict pc (\_ -> ((loc, la) ~> loc'))
  return $ labelIn result

-- | Conditionally execute choreographies based on a located value.

sputStrLn :: Show a => SPrin pc -> (l ⊑ pc) => l!a -> Labeled IO pc (pc!())
sputStrLn pc la = restrict pc (\open -> putStrLn (show $ open la))

sgetLine :: SPrin pc -> Labeled IO pc (pc!String)
sgetLine pc = restrict pc (\_ -> getLine)

safePutStrLn :: forall l a. (Show a, l ⊑ ABD) => l!a 
                      -> Labeled IO ABD (ABD!())
safePutStrLn =  sputStrLn abd

buyerGetLine :: Labeled IO ABD (ABD!String)
buyerGetLine = sgetLine abd

agetLine :: Labeled IO ABD (ABD!String)
agetLine = sgetLine abd

bgetLine :: Labeled IO ABD (ABD!String)
bgetLine = sgetLine abd 

dgetLine :: Labeled IO ABD (ABD!String)
dgetLine = sgetLine abd

--Choreo IO (Maybe Day @ "buyer")
--Labeled (Choreo IO) BS ((BS ! (FromBuyer ! Maybe Day)) @ "buyer")

choreo ::  Labeled (Choreo IO) ABD ((ABD ! String ) @ "D")
choreo = 
  do dataa <- (abd,a,abd,abd) `slocally` \_ -> agetLine
     aa <- (abd,a,abd,abd) `slocally` \un  -> safePutStrLn (un dataa)

     datab <- (abd,b,abd,abd) `slocally` \_ -> bgetLine
     bb <- (abd,b,abd,abd) `slocally` \un  -> safePutStrLn (un datab)
--Use      :: (Monad m, l' ⊑ l, l' ⊑ pc') =>
 --     l'!b -> (b -> Labeled m pc' (l!a)) -> LabeledSig m pc (l!a)
 --IO (Async a, a)
     ad  <- (sym a, abd, abd, dataa) ~>: sym d
     bd  <- (sym b, abd, abd, datab) ~>: sym d
 --  use @_ @_ @_ @BS (join @_ @_ @BS (un title'')) (\t -> protect $ contriOf t))
 -- change the ~>: itself to send Async 
     got <- (abd,d,abd,abd) `slocally` \un -> do 
         x <- (use @_ @_ @_ @ABD ((un ad)) (\t ->  protect (waitAny [t]))) --(waitAny [un ad]) --(x:Async a, y:a)
         safePutStrLn $ label ("yo")
    
     dd <- (abd,d,abd,abd) `slocally` \_ -> dgetLine
     --dd <- (abd,d,abd,abd) `slocally` \un  -> safePutStrLn (un ad)
     return dd
  
  --locD `slocally` \un -> do
  --  (x, y) <- waitAny [un a, un b] --(Async a, a)
  --  putStrLn y
    --if x == un a
     --then putStrLn "A comes first"
     --else putStrLn "B comes first"
 
  --locD `locally` \un -> putStrLn (un b)

test2 :: IO ()
test2 = do
  [loc] <- getArgs
  --case loc of
  void $ runChoreography cfg (runLabeled choreo) loc
  where
    cfg = mkHttpConfig [ ("A", ("localhost", 4246))
                       , ("B", ("localhost", 4343))
                       , ("C", ("localhost", 4444))
                       , ("D", ("localhost", 4545))
                       ]

----------------------------------------------------------------------
-- Test sequence ids
-- the new comm creates state and assigns an incremented counter to it
--- on choreographic level the async is happenning
--- whereas my idea of select was to do the do the async at EPP level

choreo2 :: Choreo IO (() @ "D")
choreo2 = do
  locA `locally` \_ -> getLine

  a1  <- (locA, wrap "Hello, ") ~> locD
  a2  <- (locB, wrap "world. ") ~> locD
  a3  <- (locC, wrap "I like ") ~> locD
  a4  <- (locA, wrap "choreographic programming.") ~> locD

  locD `locally` \un -> do
    as <- mapM (wait . un) [a2, a1, a3, a4]
    putStrLn (foldr (++) [] as)

test3 :: IO ()
test3 = do
  [loc] <- getArgs
  void $ runChoreography cfg choreo2 loc
  where
    cfg = mkHttpConfig [ ("A", ("localhost", 4242))
                       , ("B", ("localhost", 4343))
                       , ("C", ("localhost", 4444))
                       , ("D", ("localhost", 4545))
                       ]

----------------------------------------------------------------------
-- Entry point

--main = test1
main = test2
--main = test3
