{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE ExplicitNamespaces #-}

module Main where

--import MyHasChor.Choreography
import MyHasChor.Choreography.Location
import MyHasChor.Choreography.NetworkAsync
import MyHasChor.Choreography.NetworkAsync.Http
import MyHasChor.Choreography.ChoreoAsync
import Control.Concurrent.Async
import MyHasChor.Choreography.Flaqr
import MyHasChor.Choreography.Labelled
import System.Environment
import System.Timeout 
import Data.Proxy
import Control.Monad
import GHC.TypeLits
import Data.List hiding (compare)
import Data.Monoid (Last(getLast))
import GHC.Conc.IO (threadDelay)
import Prelude hiding (compare)
--import Choreography.ChoreoAsync (cond)
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


-- locA :: Proxy "A"
-- locA = Proxy

-- locB :: Proxy "B"
-- locB = Proxy

-- locC :: Proxy "C"
-- locC = Proxy

-- client :: Proxy "client"
-- client = Proxy 

type A = N "A"
locA :: SPrin A
locA = SName (Proxy :: Proxy "A")

type B = N "B"
locB :: SPrin B
locB = SName (Proxy :: Proxy "B")

type D = N "C"
locC :: SPrin D
locC = SName (Proxy :: Proxy "D")

type Client = N "client"
client :: SPrin Client
client = SName (Proxy :: Proxy "client")

type ABC = (A \/ B \/ D \/ Client) 
   --deriving (Show)

abc :: SPrin ABC
abc = locA *\/ locB *\/ locC *\/ client

type FromA = ABC 
fromA :: SPrin ABC
fromA = abc

type FromB = ABC 
fromB :: SPrin ABC
fromB = abc

type FromC = ABC 
fromC :: SPrin ABC
fromC = abc

type FromClient = ABC 
fromClient :: SPrin ABC
fromClient = abc



joinIn' :: forall l l' l'' pc m a loc. 
  (Monad m, l ⊑ l'', l' ⊑ l'', Show a, Read a) => 
  Labeled m pc (l ! ((l'!a) @ loc)) -> Labeled m pc ((l''!a) @ loc)
joinIn' lx = wrap <$> do 
  x <- lx 
  let x' = joinIn @l @l' @l'' x -- why didn't this get inferred?
  use (unwrap x') protect

(~>:) :: forall a loc loc' pc l m. (Show a, Read a, KnownSymbol loc, KnownSymbol loc')--, Show (l!a), Read (l!a)) --, (N loc') ≽ (C pc), (N loc) ≽ (I pc))
     => (Proxy loc, SPrin pc, SPrin l, (l!a) @ loc)  
                                -- a sender's location, 
                                -- a clearance, 
                                -- and a value located at the sender
     -> Proxy loc'-- ^ A receiver's location.
     -> Labeled (Choreo m) pc (Async (pc!(l!a)) @ loc')
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

--------------

majorityQuorum :: Choreo IO (Async Int @ "client")
majorityQuorum = do 
 
  client `locally` \_ -> do putStrLn "at client$"

  a <- locA `locally` \_ -> do
      putStrLn "Enter value at A::"
      readLn :: IO Int

  b <- locB `locally` \_ -> do
      putStrLn "Enter value at B::"
      readLn :: IO Int

  c <- locC `locally` \_ -> do
      putStrLn "Enter value at C::"
      readLn :: IO Int

  a' <- (locA, a) ~> client
  b' <- (locB, b) ~> client
  c' <- (locC, c) ~> client
  

  abc <- client `locally` \un -> do 
    selecT $ compare_ [un a', un b', un c'] 2

  m <- client `locally` \un -> do
    q <- wait (un abc)
    print q
    return q

  ma <- (client,m) ~> locA
  mb <- (client, m) ~> locB
  mc <- (client, m) ~> locC

  locA `locally` \un -> do
    q <- wait (un ma)
    print q

  locB `locally` \un -> do
    q <- wait (un mb)
    print q

  locC `locally` \un -> do
    q <- wait (un mc)
    print q

  --bc <- client `locally` \un -> do compare (un b') (un c')
  --ca <- client `locally` \un -> do compare (un c') (un a')
  --bcca <- client `locally` \un -> do select (un bc) (un ca)
  --abc <- client `locally` \un -> do select (un ab) (un bcca)
  client `locally` \_ -> do 
      putStrLn "consensus done"
      getLine
  return abc


majorityQuorumMain :: IO ()
majorityQuorumMain = do
  [loc] <- getArgs
  void $ runChoreography cfg majorityQuorum loc
  where
    cfg = mkHttpConfig [ ("A", ("localhost", 4240))
                       , ("B", ("localhost", 4341))
                       , ("C", ("localhost", 4544))
                       , ("client", ("localhost", 4445))
                       ]
----------------------------------------------------------------------
-- Entry point
main = majorityQuorumMain