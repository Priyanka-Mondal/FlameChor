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
import Data.Map.Internal.Debug (node)
import Data.Bits (Bits(xor))
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

pbft :: Choreo IO () --forall (a:: LocTy). (KnownSymbol a) => Seq.StateT (SystemState a) IO NodeState --Choreo IO ()
pbft = do 
  request <- client `locally` \_ -> do
      putStrLn "Enter value to be proposed:"
      readLn :: IO Int
  
  req <- (client, request) ~> leader
  req' <- leader `locally` \un -> do 
                        x <- wait (un req)
                        return x 
  (leader,req') ~> locA 
  --(ppa, ppb, ppc) <- preprepare (leader, req) locA locB locC 
  --prepare (locA, ppa) (locB, ppb) (locC, ppc)  --preprepare 
  st <- Seq.evalStateT (pprep (req, leader, locA)) (startState)
  sl <- leader `locally` \_ -> do 
    let s' = st ! "leader"
    putStrLn (show s') 
    return s'

  sa <- locA `locally` \_ -> do 
    let s' = st ! "A"
    putStrLn (show s') 
    return s'
  --checkState (locA)
  
  return () 


--type Node = Proxy a 
data NodeState = INIT | PREPREPARE | PREPARE | COMMIT | COMMITTED
  deriving (Eq, Show) 

--type StateMachine = Seq.StateT NodeState 

data SystemState =  HashMap (String) NodeState

nextState :: NodeState -> NodeState 
nextState INIT = PREPREPARE
nextState PREPREPARE = PREPARE
nextState PREPARE = COMMIT 
nextState COMMIT = COMMITTED
nextState COMMITTED = INIT 

updateState :: (Monad m) => String -> Seq.StateT ( HashMap (String) NodeState) m ( HashMap (String) NodeState) 
updateState locA = do
    current <- Seq.get
    let state = current ! locA
    let nextstate = nextState state 
    let newState =  HM.insert locA nextstate current
    Seq.put $ newState
    return (newState)

type Node = String

keys :: [Node]
keys = ["A", "B", "C", "leader"]

startState :: HM.HashMap (Node) NodeState
startState = HM.fromList [(key, INIT) | key <- keys]

pprep :: forall (a:: LocTy) (b:: LocTy) m. (KnownSymbol a, KnownSymbol b, Seq.MonadIO m) => 
                     (Async (Int) @ a, Proxy a, Proxy b) -> Seq.StateT ( HashMap (String) NodeState) (Choreo m) ( HashMap (String) NodeState)
pprep (req, locl, loc) =  do
                           req' <- Seq.lift (locl `locally` \un -> do 
                              x <-  Seq.liftIO $ wait (un req) 
                              return x )
                           prepa <- Seq.lift ((locl,req') ~> loc)
                           updateState (proxyToString locl) >> prep (loc, prepa) 

prep :: forall (a:: LocTy) m. (KnownSymbol a, Seq.MonadIO m) => 
                     (Proxy a, Async Int @ a) -> Seq.StateT ( HashMap (String) NodeState) (Choreo m) ( HashMap (String) NodeState)
prep (locl, msg) =  do
                    req' <- Seq.lift (locl `locally` \un -> do 
                              x <-  Seq.liftIO $ wait (un msg) 
                              Seq.liftIO $ putStrLn $ "mymsg:" ++ (show x)
                              return x )
                    updateState (proxyToString locl)                           
                      
runStateTInIO :: Seq.StateT Int IO Int -> IO Int
runStateTInIO computation = Seq.evalStateT computation 0

newRand = randomIO :: IO Int      

proxyToString :: forall a. KnownSymbol a => Proxy a -> String
proxyToString _ = symbolVal (Proxy @a)
-- Async (Int, Int, String) @ b, Async (Int, Int, String) @ c, Async (Int, Int, String) @ d

{--checkState :: forall (a:: LocTy). (KnownSymbol a) => (Proxy a) 
              -> Seq.StateT (SystemState) IO NodeState
checkState loc = do 
            let s = proxyToString loc 
            updateState s >>= \x -> Seq.lift (do 
                                              putStrLn "yayyy"
                                              return ((x) ! s))
            --let arraystate = nodeState current 
            --let state = arraystate ! s 
            --return state 
--}

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
  void $ runChoreography cfg pbft loc -- >> (pBFTMain cfg)
 
preprep :: String
preprep = "preprepare"


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