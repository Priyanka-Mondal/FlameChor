{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase     #-}

module Main where

--import MyHasChor.Choreography
import MyHasChor.Choreography.Location
import MyHasChor.Choreography.NetworkAsync
import MyHasChor.Choreography.NetworkAsync.Http
import MyHasChor.Choreography.ChoreoAsync
import Control.Concurrent.Async
import MyHasChor.Choreography.Flaqr
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


locA :: Proxy "A"
locA = Proxy

locB :: Proxy "B"
locB = Proxy

locC :: Proxy "C"
locC = Proxy

client :: Proxy "client"
client = Proxy 


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
    selecT $ compare_ [un c', un c', un c'] 2

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