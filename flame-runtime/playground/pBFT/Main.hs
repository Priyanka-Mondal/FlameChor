{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

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
import Control.Monad.State qualified as Seq
import Data.IORef
import System.Random
import qualified Data.Array as A
import Data.HashMap.Strict qualified as HM
import Data.HashMap.Strict (HashMap, (!), insert) 
--import Control.Monad.StateT qualified as SeqT
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
  preprepare (leader, req) locA locB locC 
  --prepare --preprepare 
  --- after this the state of all nodes 
  {--printAll locA locB locC (ppa, ppb, ppc)

  (pab, pac, pal) <- prepare (locA, ppa) locB locC leader  -- prepare from A
  (pba, pbc, pbl) <- prepare (locB, ppb) locA locC leader  -- prepare from B
  (pca, pcb, pcl) <- prepare (locC, ppc) locA locB leader  -- prepare from C
  (pla, plb, plc) <- prepare (leader, ppl) locA locB locC

  (cab, cac, cal) <- prepare (locA, ppa) locB locC leader  -- commit from A
  (cba, cbc, cbl) <- prepare (locB, ppb) locA locC leader  -- commit from B
  (cca, ccb, ccl) <- prepare (locC, ppc) locA locB leader  -- commit from C
  (cla, clb, clc) <- prepare (leader, ppl) locA locB leader  -- commit from leader
  --}

  return () 


--type Node = Proxy a 
data NodeState = INIT | PREPREPARE | PREPARE | COMMIT 
  deriving (Eq, Show) 

--type StateMachine = Seq.StateT NodeState 

data SystemState a = SystemState 
  { nodeState :: HashMap (String) NodeState
  --, currentNode :: Proxy a 
  }

nextState :: NodeState -> NodeState 
nextState INIT = PREPREPARE
nextState PREPREPARE = PREPARE
nextState PREPARE = COMMIT 
nextState COMMIT = INIT 

updateState :: String -> Seq.StateT (SystemState a)  IO (SystemState a)
updateState locA = do
    current <- Seq.get
    let arraystate = nodeState current 
    let state = arraystate ! locA
    let nextstate = nextState state 
    let newState =  HM.insert locA nextstate arraystate
    Seq.liftIO $ print state
    Seq.put $ current {nodeState = newState}
    return (current)

type Node = String

keys :: [Node]
keys = ["A", "B", "C", "leader"]

-- Create the initial HashMap
startState :: HM.HashMap (Node) NodeState
startState = HM.fromList [(key, INIT) | key <- keys]

getNextNumber :: Seq.StateT Int IO Int
getNextNumber = do
    current <- Seq.get
    Seq.put (current + 1)
    Seq.liftIO $ putStrLn $ show current
    return (current)

runStateTInIO :: Seq.StateT Int IO Int -> IO Int
runStateTInIO computation = Seq.evalStateT computation 0

newRand = randomIO :: IO Int      

-- Async (Int, Int, String) @ b, Async (Int, Int, String) @ c, Async (Int, Int, String) @ d
prepare :: forall (a :: LocTy) (b :: LocTy) (c :: LocTy) (d :: LocTy). 
           (KnownSymbol a, KnownSymbol b, KnownSymbol c, KnownSymbol d) =>
           (Proxy a, Async (Int,Int,String) @ a) 
           -> Proxy b -> Proxy c -> Proxy d 
           -> Choreo IO (Async (Int, Int, String) @ b, Async (Int, Int, String) @ c, Async (Int, Int, String) @ d)
prepare (loca,msg) locb locc locd = do
    req' <- loca `locally` \un -> do 
                                   (i, j, st) <- wait $ un msg
                                   if (st == preprep) then 
                                     return (i,j,prep) -- need to return a seq
                                   else return (i,j,"NULL")
    ppa <- (loca, req') ~> locb
    ppb <- (loca, req') ~> locc
    ppd <- (loca, req') ~> locd
    loca `locally` \_ -> putStrLn "prepare at A done"
    return (ppa, ppb, ppd)

type family TypeName (a :: *) :: Symbol where
  TypeName (Proxy "A") = "A"
  TypeName (Proxy "B") = "B"
  TypeName (Proxy "C") = "C"
  TypeName (Proxy "D") = "D"

class Transform a where
  transform :: (a) -> String

instance Transform (Proxy "A") where
  transform (locA) = "A"

instance Transform (Proxy "B") where
  transform (locB) = "B"

instance Transform (Proxy "C") where
  transform (locB) = "C"

instance Transform (Proxy "leader") where
  transform (locB) = "leader"
  

transformTo :: forall a. Transform a => a -> String
transformTo = transform
{--
stringToInt1 :: String -> Int
stringToInt1 = transform . transformTo @Double

stringToInt2 :: String -> Int
stringToInt2 = transform . transformTo @Rational
--typeName :: forall a. KnownSymbol a => String
--typeName = symbolVal (Proxy @(TypeName (Proxy a)))
--}

{--nodeToString :: Proxy a -> String
nodeToString locA = "A"
nodeToString locB = "B"
nodeToString locC = "C"
nodeToString locD = "leader"
--}
preprepare :: forall (a :: LocTy) (b :: LocTy) (c :: LocTy) (d :: LocTy). (KnownSymbol a, KnownSymbol b, KnownSymbol c, KnownSymbol d) =>
          (Proxy a, Async Int @ a) -> Proxy b -> Proxy c -> Proxy d -> Choreo IO ()
preprepare (loca, req) locb locc locd = do
  req' <- loca `locally` \un -> do 
                                r <- wait $ un req
                                let b = updateState ("leader") -- >>= \x -> return x
                                putStrLn $ "leader sent:" ++ show r
                                let s = transformTo (loca)
                                return r
  
  pa <- (loca, req') ~> locb
  ppb <- (loca, req') ~> locc
  ppc <- (loca, req') ~> locd
  ppd <- (loca, req') ~> loca
  return ()

pre_prepare :: forall (a :: LocTy) (b :: LocTy) (c :: LocTy) (d :: LocTy). (KnownSymbol a, KnownSymbol b, KnownSymbol c, KnownSymbol d) =>
          Proxy a -> Proxy b -> Proxy c -> Proxy d -> Async Int @ a -> Choreo IO (Async (Int, Int, String) @ b, Async (Int, Int, String) @ c,
                                 Async (Int, Int, String) @ d, Async (Int, Int, String) @ a)
pre_prepare loca locb locc locd req = do
  req' <- loca `locally` \un -> do 
                                   r <- wait $ un req
                                   let by = getNextNumber >>= \x -> return x
                                   num <- newRand
                                   return (r, num, preprep) -- need to return a seq#
  ppa <- (loca, req') ~> locb
  ppb <- (loca, req') ~> locc
  ppc <- (loca, req') ~> locd
  ppd <- (loca, req') ~> loca
  loca `locally` \_ -> putStrLn "sent"
  return (ppa, ppb, ppc, ppd)


printAll :: forall (a :: LocTy) (b :: LocTy) (c :: LocTy). (KnownSymbol a, KnownSymbol b, KnownSymbol c) =>
          Proxy a -> Proxy b -> Proxy c -> (Async (Int, Int, String) @ a, Async (Int, Int, String) @ b,
                                 Async (Int,Int, String) @ c) -> Choreo IO ()
printAll loca locb locc (ppa, ppb, ppc) = do
  loca `locally` \un -> do 
                         r <- wait $ un ppa
                         putStrLn (show r)
  locb `locally` \un -> do 
                         r <- wait $ un ppb
                         putStrLn (show r)

  locc `locally` \un -> do 
                         r <- wait $ un ppc
                         putStrLn (show r) 
  return ()

pBFTMain :: HttpConfig -> IO ()
pBFTMain cfg = do
  [loc] <- getArgs
  void $ runChoreography cfg pbft loc >> (pBFTMain cfg)
 
preprep :: String
preprep = "preprepare"
prep :: String
prep = "prepare"

main = do 
  pBFTMain cfg 
 where
    cfg = mkHttpConfig [ ("A", ("localhost", 4242))
                       , ("B", ("localhost", 4343))
                       , ("C", ("localhost", 4544))
                       , ("leader", ("localhost", 4545))
                       , ("client", ("localhost", 4546))
                       ]

type GameValue = Int
type GameState = (Bool, Int)

playGame :: [String] -> Seq.State GameState GameValue
playGame []     = do
    (_, score) <- Seq.get
    return score

playGame (x:xs) = do
    (on, score) <- Seq.get
    case x of
         "prepare" | on -> Seq.put (on, score + 1)
         "commit" | on -> Seq.put (on, score - 1)
         _        -> Seq.put (on, score)
    playGame xs



--main = print $ Seq.evalState (playGame ["cbbbcaacaa"]) (False, 0)