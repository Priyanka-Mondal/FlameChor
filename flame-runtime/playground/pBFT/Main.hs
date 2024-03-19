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

leader :: Proxy "leader"
leader = Proxy

client :: Proxy "client"
client = Proxy 

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

pbft :: Choreo IO ()
pbft = do 
  request <- client `locally` \_ -> do
      putStrLn "Enter value to be proposed:"
      readLn :: IO Int
  
  req <- (client, request) ~> leader
  (ppa, ppb, ppc) <- pre_prepare req
  
  printAll (ppa, ppb, ppc)

  return () 

pre_prepare :: Async Int @ "leader" -> Choreo IO (Async (Int, String) @ "A", Async (Int, String) @ "B",
                                 Async (Int, String) @ "C")
pre_prepare req = do
  req' <- leader `locally` \un -> do 
                                   r <- wait $ un req
                                   return (r, preprep) 
  ppa <- (leader, req') ~> locA
  ppb <- (leader, req') ~> locB
  ppc <- (leader, req') ~> locC
  leader `locally` \_ -> putStrLn "sent"
  return (ppa, ppb, ppc)



printAll ::  (Async (Int, String) @ "A", Async (Int, String) @ "B",
                                 Async (Int, String) @ "C") -> Choreo IO ()
printAll (ppa, ppb, ppc) = do
  locA `locally` \un -> do 
                         r <- wait $ un ppa
                         putStrLn (show r)
  locB `locally` \un -> do 
                         r <- wait $ un ppb
                         putStrLn (show r)

  locC `locally` \un -> do 
                         r <- wait $ un ppc
                         putStrLn (show r)
                    
  return ()

pBFTMain :: HttpConfig -> IO ()
pBFTMain cfg = do
  [loc] <- getArgs
  void $ runChoreography cfg pbft loc >> (pBFTMain cfg)
 
preprep :: String
preprep = "preprepare"

main = pBFTMain cfg 
 where
    cfg = mkHttpConfig [ ("A", ("localhost", 4242))
                       , ("B", ("localhost", 4343))
                       , ("C", ("localhost", 4544))
                       , ("leader", ("localhost", 4545))
                       , ("client", ("localhost", 4546))
                       ]
