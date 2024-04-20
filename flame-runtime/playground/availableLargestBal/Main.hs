{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PostfixOperators, TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}


module Main where

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
  
  client `locally` \un -> do 
    a <- wait $ un availBal
    putStrLn $ "availBal:" ++ show a
    
  larAv <- client `locally` \un -> do getLargest (un bal1') (un bal2')

  client `locally` \un -> do 
    a <- wait $ un larAv
    putStrLn $ "larAv:" ++ show a
    
  largestAvailBal <- client `locally` \un -> select (un larAv) (un availBal) 

  client `locally` \un -> do 
    a <- wait $ un largestAvailBal
    putStrLn $ "largestAvailBal:" ++ show a
    
  decision <- client `locally` \un -> do
     a <- wait (un largestAvailBal)
     print a           
     return (a < 100)

  cond (client, decision) \case
         a -> do
           b1 `locally` \_ -> do 
                              a' <- wait a
                              putStrLn $ "less than 100 @b1:" ++ show a'
           b2 `locally` \_ -> do 
                              a' <- wait a
                              putStrLn $ "less than 100 @b2:" ++ show a'
           client `locally` \_ -> do 
                                a' <- wait a
                                putStrLn $ "less than 100 @client:" ++ show a'
                                getLine 
   

  return largestAvailBal



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

  ab <- client `locally` \un -> do compare_ [un a', un b', un c', un d', un e'] 3
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

--main = threeByFiveQuorumMain
main = availableLargestBalance