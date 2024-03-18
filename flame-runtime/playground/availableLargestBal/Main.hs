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

locD :: Proxy "D"
locD = Proxy

locE :: Proxy "E"
locE = Proxy


b1 :: Proxy "b1"
b1 = Proxy 

b2 :: Proxy "b2"
b2 = Proxy 

client :: Proxy "client"
client = Proxy 


availLarBal :: Choreo IO (Async Int @ "client")
availLarBal = do 
  bal1 <-
    b1 `locally` \_ -> do
      putStrLn "Enter bal1 at bank1::"
      readLn :: IO Int

  bal2 <-
    b2 `locally` \_ -> do
      putStrLn "Enter bal2 at bank2::"
      readLn :: IO Int
  
  bal1' <- (b1, bal1) ~> client
  bal2' <- (b2, bal2) ~> client
  availBal <- client `locally` \un -> do select (un bal1') (un bal2') 
  larAv <- client `locally` \un -> do getLargest (un bal1') (un bal2')
  largestAvailBal <- client `locally` \un -> select (un larAv) (un availBal) 
  decision <- client `locally` \un -> do
    a <- wait (un largestAvailBal)
    putStrLn (show a)           
    return (a < 100)
  
  decision <- client `locally` \_ -> do
    return True

  cond (client, decision) do
        b <- wait decision
        case b of 
         True -> do
           b1 `locally` \_ -> putStrLn "less than 100 b1" 
           return Nothing 
         False -> do
           return Nothing

  return largestAvailBal

majorityQuorum :: Choreo IO (Async Int @ "client")
majorityQuorum = do 
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

  ab <- client `locally` \un -> do compare (un a') (un b')
  bc <- client `locally` \un -> do compare (un b') (un c')
  ca <- client `locally` \un -> do compare (un c') (un a')

  bcca <- client `locally` \un -> do select (un bc) (un ca)
  abc <- client `locally` \un -> do select (un ab) (un bcca)
    
  client `locally` \un -> do
    q <- wait (un abc)
    putStrLn (show q) 
  return abc


threeByFiveQuorum :: Choreo IO (Async Int @ "client")
threeByFiveQuorum = do 
  a <- locA `locally` \_ -> do
      putStrLn "Enter value at A::"
      readLn :: IO Int

  b <- locB `locally` \_ -> do
      putStrLn "Enter value at B::"
      readLn :: IO Int

  c <- locC `locally` \_ -> do
      putStrLn "Enter value at C::"
      readLn :: IO Int
  
  d <- locD `locally` \_ -> do
      putStrLn "Enter value at D::"
      readLn :: IO Int

  e <- locE `locally` \_ -> do
      putStrLn "Enter value at E::"
      readLn :: IO Int

  a' <- (locA, a) ~> client
  b' <- (locB, b) ~> client
  c' <- (locC, c) ~> client
  d' <- (locD, d) ~> client
  e' <- (locE, e) ~> client

  ab <- client `locally` \un -> do compare_ [(un a'), (un b'), (un c'), (un d'), (un e')] 3
  abc <- client `locally` \un -> do select_ (un ab)
  
  client `locally` \un -> do
    q <- wait (un abc)
    putStrLn ("majority 3/5 quorum:" ++ show q) 
  return abc

availableLargestBalance :: IO ()
availableLargestBalance = do
  [loc] <- getArgs
  void $ runChoreography cfg availLarBal loc
  where
    cfg = mkHttpConfig [ ("b1", ("localhost", 4242))
                       , ("b2", ("localhost", 4343))
                       , ("client", ("localhost", 4444))
                       ]

threeByFiveQuorumMain :: IO ()
threeByFiveQuorumMain = do
  [loc] <- getArgs
  void $ runChoreography cfg threeByFiveQuorum loc
  where
    cfg = mkHttpConfig [ ("A", ("localhost", 4242))
                       , ("B", ("localhost", 4343))
                       , ("C", ("localhost", 4544))
                       , ("D", ("localhost", 4445))
                       , ("E", ("localhost", 4446))
                       , ("client", ("localhost", 4447))
                       ]

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
--main = test3
--main = threeByFiveQuorumMain
main = availableLargestBalance