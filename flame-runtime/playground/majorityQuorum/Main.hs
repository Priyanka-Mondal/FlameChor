{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase     #-}

module Main where

import Choreography.Location
import Choreography.NetworkAsync
import Choreography.NetworkAsync.Http
import Choreography.ChoreoAsync
import Control.Concurrent.Async
import Choreography.Flaqr
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

  a' <- (locA, a) ~> locB
  b' <- (locB, b) ~> locA
  c' <- (locC, c) ~> client

  locB `locally` \un -> do
   a <- wait $ un a'
  -- b <- wait $ un b'
  -- c <- wait $ un c' 
   putStrLn $ ": "++ show a -- ++ " /" ++ show b ++ "/ " ++ show c


  client `locally` \_ -> do putStrLn "waiting client$"

  abc <- client `locally` \un -> do selecT $ compare_ [un b', un b', un c'] 1
  --bc <- client `locally` \un -> do compare (un b') (un c')
  --ca <- client `locally` \un -> do compare (un c') (un a')
 
  client `locally` \_ -> do putStrLn "compared client$"

  --bcca <- client `locally` \un -> do select (un bc) (un ca)
  --abc <- client `locally` \un -> do select (un ab) (un bcca)
    
  client `locally` \_ -> do putStrLn "selected client$"
  
  client `locally` \un -> do
    q <- wait (un abc)
    putStrLn $ show q
  return abc


majorityQuorumMain :: IO ()
majorityQuorumMain = do
  [loc] <- getArgs
  void $ runChoreography cfg majorityQuorum loc
  where
    cfg = mkHttpConfig [ ("A", ("localhost", 4242))
                       , ("B", ("localhost", 4343))
                       , ("C", ("localhost", 4544))
                       , ("client", ("localhost", 4445))
                       ]
----------------------------------------------------------------------
-- Entry point
main = majorityQuorumMain