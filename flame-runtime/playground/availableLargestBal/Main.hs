{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BlockArguments #-}

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

-- 1. `Async a` denotes a asynchornous computation that returns a
-- value of type `a`. There's a set of functions to work with `Async`,
-- like `wait`, `waitAny`.

-- 2. Asynchrony is completely done at the local language level with
-- comm (~>) returnning a Async. `wait` is a local langauge function.

-- 3. Send and recv in the network programs are explicitly marked with
-- a sequence id to connect received messages to `Async`s. This is
-- very similar to the counter in our operational semantics except
-- it's statically calculated.
--
-- Example:
--
-- A:                             B:
--   send "hello" B                 x <- recv A
--   send "world" B                 y <- recv A
--                                  print (x ++ y)
--
-- Question: What should B print?
--
--
-- A:                             B:
--   send "hello" B 1000            x <- recv A 1000
--   send "world" B 1001            y <- recv A 1001
--                                  print (x ++ y)
--
-- B should print "helloworld"

-- 4. `epp` is responsible for generating sends and receives with
-- mathching sequence numbers.

-- 5. The HTTP backend uses a message buffer to store received
-- messages, which is a map from (LocTm, SeqId) to messages.

----------------------------------------------------------------------
-- Test asynchronous network programs

progA :: Network IO ()
progA = do
  lift $ getLine
  send () "D" 1000
  return ()

progB :: Network IO ()
progB = do
    lift $ getLine
    send () "D" 1000
    return ()

progC :: Network IO ()
progC = do
    lift $ getLine
    send () "D" 1000
    return ()

progD :: Network IO ()
progD = do
  (a :: Async ()) <- recv "A" 1000
  (b :: Async ()) <- recv "B" 1000
  (c :: Async ()) <- recv "C" 1000
  lift $ putStrLn "I can do something else while waiting!"
  (x, _) <- lift $ waitAny [a, b, c]
  if x == a
    then lift $ putStrLn "A comes first"
    else if x == b
         then lift $ putStrLn "B comes first"
         else lift $ putStrLn "C comes first"

test1 :: IO ()
test1 = do
  [loc] <- getArgs
  case loc of
    "A" -> runNetwork cfg "A" progA
    "B" -> runNetwork cfg "B" progB
    "C" -> runNetwork cfg "C" progC
    "D" -> runNetwork cfg "D" progD
  return ()
  where
    cfg = mkHttpConfig [ ("A", ("localhost", 4242))
                       , ("B", ("localhost", 4343))
                       , ("C", ("localhost", 4444))
                       , ("D", ("localhost", 4545))
                       ]

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

locE :: Proxy "E"
locE = Proxy

choreo :: Choreo IO (() @ "D")
choreo = do
  locA `locally` \_ -> getLine
  a  <- (locA, wrap ("hi from A")) ~> locD

  locB `locally` \_ -> getLine
  b  <- (locB, wrap ("hi from B")) ~> locD

  locC `locally` \_ -> getLine
  c  <- (locC, wrap ("hi from C")) ~> locD

  locD `locally` \un -> putStrLn "I can do something else while waiting!"
  locD `locally` \un -> getLine
-- timeout with waitEither is basically select
  locD `locally` \un -> do
    x <- timeout 10000000 (waitEither (un a) (un b))
    case x of 
      Nothing -> putStrLn "Nothing"
      Just e -> case e of 
        Left l -> putStrLn l 
        Right r -> putStrLn r


test2 :: IO ()
test2 = do
  [loc] <- getArgs
  void $ runChoreography cfg choreo loc
  where
    cfg = mkHttpConfig [ ("A", ("localhost", 4242))
                       , ("B", ("localhost", 4343))
                       , ("C", ("localhost", 4444))
                       , ("D", ("localhost", 4545))
                       ]

----------------------------------------------------------------------
-- Test sequence ids

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
--async :: IO a -> IO (Async a)
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
  client `locally` \un -> do
    a <- wait (un largestAvailBal)
    putStrLn (show a)           
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
--main = test1
--main = test2
--main = test3
main = threeByFiveQuorumMain
