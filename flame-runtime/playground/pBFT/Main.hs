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

type Node = String

keys :: [Node]
keys = ["A", "B", "C", "leader"]

proxyToString :: forall a. KnownSymbol a => Proxy a -> String
proxyToString _ = symbolVal (Proxy @a)

pbft :: Choreo IO () --forall (a:: LocTy). (KnownSymbol a) => Seq.StateT (SystemState a) IO NodeState --Choreo IO ()
pbft = do 
  request <- client `locally` \_ -> do
      putStrLn "Client$ Enter value to be proposed:"
      readLn :: IO Int
  
  req <- (client, request) ~> leader
  req' <- leader `locally` \un -> do 
                        x <- wait (un req)
                        return x 
  st <- Seq.evalStateT (pprep (req', leader, locA, locB, locC)) (startState, ())
  
  sl <- leader `locally` \_ -> do 
    let s' = fst st ! "leader"
    putStrLn (show s') 
    return s'

  sa <- locA `locally` \_ -> do 
    let s' = fst st ! "A"
    putStrLn (show s') 
    return s'

  sb <- locB `locally` \_ -> do 
    let s' = fst st ! "B"
    putStrLn (show s') 
    return s'

  sc <- locC `locally` \_ -> do 
    let s' = fst st ! "C"
    putStrLn (show s') 
    return s'

  lc <- (leader, sl) ~> client
  ac <- (locA, sa) ~> client 
  bc <- (locB, sb) ~> client 
  cc <- (locC, sc) ~> client 

  ab <- client `locally` \un -> do compare_ [(un lc), (un ac), (un bc), (un cc)] 2
  abc <- client `locally` \un -> do select_ (un ab)

  c <- client `locally` \un -> do 
    finalState <- wait $ un abc 
    putStrLn $ "Client$ final state:" ++ (show finalState) 
 
  return () 

nextState :: NodeState -> NodeState 
nextState INIT = PREPREPARE
nextState PREPREPARE = PREPARE
nextState PREPARE = COMMIT 
nextState COMMIT = COMMITTED
nextState COMMITTED = INIT 

updateState :: (Monad m) => String -> Seq.StateT ((HashMap (String) NodeState), ()) m (HashMap (String) NodeState, ()) 
updateState locA = do
    current <- Seq.get
    let state = fst current ! locA
    let nextstate = nextState state 
    let newState =  HM.insert locA nextstate (fst current)
    Seq.put $ (newState, ())
    return (newState, ())

startState :: HM.HashMap (Node) NodeState
startState = HM.fromList [(key, INIT) | key <- keys]

pprep :: forall (a:: LocTy) (b:: LocTy) (c :: LocTy) (d :: LocTy) m. (KnownSymbol a, KnownSymbol b, KnownSymbol c, KnownSymbol d, Seq.MonadIO m) => 
                     ((Int) @ a, Proxy a, Proxy b, Proxy c, Proxy d) 
    -> Seq.StateT ((HashMap (String) NodeState), ()) (Choreo m) ((HashMap (String) NodeState), ())
pprep (req, locl, loca, locb, locc) =  do
                           prepa <- Seq.lift ((locl,req) ~> loca)
                           prepb <- Seq.lift ((locl, req) ~> locb)  
                           prepc <- Seq.lift ((locl, req) ~> locc)
                           updateState (proxyToString locl)  
                            >> prepare (locl, req) (loca, prepa) (locb, prepb) (locc, prepc) 

prepare :: forall (l:: LocTy) (a:: LocTy) (b:: LocTy) (c :: LocTy) m. (KnownSymbol l, KnownSymbol a, KnownSymbol b, KnownSymbol c, Seq.MonadIO m) => 
                     (Proxy l, Int @ l) -> (Proxy a, Async Int @ a) ->  (Proxy b, Async Int @ b) ->  (Proxy c, Async Int @ c)  
        -> Seq.StateT ((HashMap (String) NodeState), ()) (Choreo m) ((HashMap (String) NodeState), ())
prepare (locl, req) (loca, msga) (locb, msgb) (locc, msgc) =  do
                    Seq.lift (locl `locally` \un -> do  
                              Seq.liftIO $ putStrLn $ "prepare Leader:" ++ (show $ un req)
                              return ())
                    la <- Seq.lift ((locl, req) ~> loca)
                    lb <- Seq.lift ((locl, req) ~> locb)
                    lc <- Seq.lift ((locl, req) ~> locc)
                    updateState (proxyToString locl) 
                    
                    reqa <- Seq.lift (loca `locally` \un -> do 
                              x <-  Seq.liftIO $ wait (un msga) 
                              Seq.liftIO $ putStrLn $ "prepare A:" ++ (show x)
                              return x )
                    al <- Seq.lift ((loca, reqa) ~> locl)
                    ab <- Seq.lift ((loca, reqa) ~> locb)
                    ac <- Seq.lift ((loca, reqa) ~> locc)
                    updateState (proxyToString loca) 

                    reqb <- Seq.lift (locb `locally` \un -> do 
                              x <-  Seq.liftIO $ wait (un msgb) 
                              Seq.liftIO $ putStrLn $ "prepare B:" ++ (show x)
                              return x )
                    bl <- Seq.lift ((locb, reqb) ~> locl)
                    ba <- Seq.lift ((locb, reqb) ~> loca)
                    bc <- Seq.lift ((locb, reqb) ~> locc)
                    updateState (proxyToString locb)   

                    reqc <- Seq.lift (locc `locally` \un -> do 
                              x <-  Seq.liftIO $ wait (un msgc) 
                              Seq.liftIO $ putStrLn $ "prepare C:" ++ (show x)
                              return x )
                    cl <- Seq.lift ((locc, reqc) ~> locl)
                    ca <- Seq.lift ((locc, reqc) ~> loca)
                    cb <- Seq.lift ((locc, reqc) ~> locb)
                    updateState (proxyToString locc)                            
                      >> commit (locl, [al, bl, cl]) (loca, [la, ba, ca]) (locb, [lb, ab, cb]) (locc, [lc, ac, bc])

commit :: forall (l::LocTy) (a :: LocTy) (b :: LocTy) (c :: LocTy) m. 
          (KnownSymbol l, KnownSymbol a, KnownSymbol b, KnownSymbol c, Seq.MonadIO m) => 
          (Proxy l, [Async Int @ l]) -> (Proxy a, [Async Int @ a]) -> (Proxy b, [Async Int @ b]) -> (Proxy c, [Async Int @ c]) 
          -> Seq.StateT ((HashMap (String) NodeState), ()) (Choreo m) ((HashMap (String) NodeState), ())
commit  (locl, ls) (loca, as) (locb, bs) (locc, cs) =  do 
    -- check the messages 
    updateState (proxyToString locl)


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
  void $ runChoreography cfg pbft loc  -- >> (pBFTMain cfg)
 
main = do 
  pBFTMain cfg 
 where
    cfg = mkHttpConfig [ ("A", ("localhost", 4242))
                       , ("B", ("localhost", 4343))
                       , ("C", ("localhost", 4544))
                       , ("leader", ("localhost", 4545))
                       , ("client", ("localhost", 4546))
                       ]
