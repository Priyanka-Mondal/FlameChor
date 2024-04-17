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
import MyHasChor.Choreography.LabelledAsync
import System.Environment
import System.Timeout 
import Data.Proxy
--import Control.Monad
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
locC = SName (Proxy :: Proxy "C")

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


safePutStrLn :: forall l a. (Show a, l ⊑ ABC) => l!a 
                      -> Labeled IO ABC (ABC!())
safePutStrLn =  sPutStrLn  abc

aGetLine :: Labeled IO FromA (FromA ! Int)
aGetLine = strGetLine fromA

bGetLine :: Labeled IO FromB (FromB ! Int)
bGetLine = strGetLine fromB

cGetLine :: Labeled IO FromC (FromC ! Int)
cGetLine = strGetLine fromB
--------------
--------------

majorityQuorum :: Labeled (Choreo IO) ABC ((ABC ! (FromClient ! Int)) @ "client")
majorityQuorum = do 
 
  title <-(abc, client, abc, fromClient) `sLocally` (\_ -> do
             safePutStrLn @ABC $ label "at client$")

  --client `locally` \_ -> do putStrLn "at client$"

  a <- (abc, locA, abc, fromA) `sLocally` (\_ -> do
             safePutStrLn @ABC $ label "Enter value at A::"
             relabel' abc aGetLine)

  -- a <- locA `locally` \_ -> do
  --     putStrLn "Enter value at A::"
  --     readLn :: IO Int

  b <- (abc, locB, abc, fromB) `sLocally` (\_ -> do
             safePutStrLn @ABC $ label "Enter value at B::"
             relabel' abc bGetLine)
  -- b <- locB `locally` \_ -> do
  --     putStrLn "Enter value at B::"
  --     readLn :: IO Int
  c <- (abc, locC, abc, fromC) `sLocally` (\_ -> do
             safePutStrLn @ABC $ label "Enter value at C::"
             relabel' abc cGetLine)
  -- c <- locC `locally` \_ -> do
  --     putStrLn "Enter value at C::"
  --     readLn :: IO Int
  a' <- (sym locA, abc, fromA, a) ~>: sym client
  b' <- (sym locB, abc, fromB, b) ~>: sym client
  c' <- (sym locC, abc, fromC, c) ~>: sym client
 
  -- price <- (abc, client, abc, fromClient) `sLocally` (\un -> do
  --   use @_ @_ @_ @ABC ((joinOutAsync @ABC @ABC @ABC @Int @"client" (un a'))) (\t -> do
  --                                     z <- wait t
  --                                     protect $ times3 t))
  {--
  -- title is (BS ! (BS ! String)) @ seller
  --  price <- (bs, seller, bs, fromSeller) `slocally` (\un -> do
  --   use @_ @_ @_ @BS (join @_ @_ @BS (un title')) (\t -> protect $ priceOf t))
  -- abc <- (abc, client, abc, fromClient) `sLocallyAsync` \un -> do 
  --   relabel' abc $ selecT $ compare_ [un a', un b', un c'] 2
--Expected: Labeled IO pc'0 (l0 ! (FromClient ! Int))
--    Actual: IO (Async a0)
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
  --}


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

times3 :: Int -> Int
times3 x = 3*x 

main = majorityQuorumMain