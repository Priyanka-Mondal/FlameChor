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

def :: Int
def = 0

type Node = String

keys :: [Node]
keys = ["A", "B", "C", "leader"]

proxyToString :: forall a. KnownSymbol a => Proxy a -> String
proxyToString _ = symbolVal (Proxy @a)

times3 :: Int -> Int
times3 x =  x*3 

pbft :: Choreo IO () --forall (a:: LocTy). (KnownSymbol a) => Seq.StateT (SystemState a) IO NodeState --Choreo IO ()
pbft = do 
  request <- client `locally` \_ -> do
      putStrLn "Client$ Enter value to be proposed:"
      readLn :: IO Int
  
  req <- (client, request) ~> leader
  st <- Seq.evalStateT (preprepare (req, leader, locA, locB, locC)) (startState, startReply)
  
  --printing local states at the end
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

-- client checking if there are 2f+1 matching results
  ab <- client `locally` \un -> do compare_ [(un lc), (un ac), (un bc), (un cc)] 2
  abc <- client `locally` \un -> do select_ (un ab)

  c <- client `locally` \un -> do 
    finalState <- wait $ un abc 
    putStrLn $ "Client$ final state:" ++ (show finalState) 
    return (finalState == COMMIT)
 

  return () 


nextState :: NodeState -> NodeState 
nextState INIT = PREPREPARE
nextState PREPREPARE = PREPARE
nextState PREPARE = COMMIT 
nextState COMMIT = COMMITTED
nextState COMMITTED = INIT 

updateState :: (Monad m) => String -> Int -> Seq.StateT ((HashMap (String) NodeState), (HashMap (String) (Int))) m (HashMap (String) NodeState, ((HashMap (String) (Int)))) 
updateState locA x = do
    current <- Seq.get
    let state = fst current ! locA
    let nextstate = nextState state 
    let newState =  HM.insert locA nextstate (fst current)
    Seq.put (newState, snd current)
    return (newState, snd current)

updateA :: (Seq.StateT NodeState m (Choreo IO NodeState)) @ "A"
updateA = do
  locA `locally` \_ -> do 
    current <- Seq.get
    let nextstate = nextState current
    Seq.put nextstate
    return nextstate


{--updateA :: forall (a:: LocTy) m. (KnownSymbol a, Monad m) => Proxy a -> Choreo IO ((Seq.StateT NodeState m NodeState) @ a)
updateA loca = do
  loca `locally` \_ -> do 
    current <- Seq.get
    let nextstate = nextState current 
    Seq.put $ current
    return nextState
  --}

startState :: HM.HashMap (Node) NodeState
startState = HM.fromList [(key, INIT) | key <- keys]

startReply :: HM.HashMap (Node) Int
startReply = HM.fromList [(key, def) | key <- keys]

preprepare :: forall (a:: LocTy) (b:: LocTy) (c :: LocTy) (d :: LocTy) m. (KnownSymbol a, KnownSymbol b, KnownSymbol c, KnownSymbol d, Seq.MonadIO m) => 
                     (Async Int @ a, Proxy a, Proxy b, Proxy c, Proxy d) 
    -> Seq.StateT ((HashMap (String) NodeState), (HashMap (String) (Int))) (Choreo m) ((HashMap (String) NodeState), (HashMap (String) ( Int)))
preprepare (req, locl, loca, locb, locc) =  do
                           req' <- Seq.lift (locl `locally` \un -> do 
                              x <-  Seq.liftIO $ wait (un req) 
                              return x ) 
                           prepa <- Seq.lift ((locl,req') ~> loca)
                           prepb <- Seq.lift ((locl, req') ~> locb)  
                           prepc <- Seq.lift ((locl, req') ~> locc)
                           updateState (proxyToString locl) def 
                            >> prepare (locl, req) (loca, prepa) (locb, prepb) (locc, prepc) 

prepare :: forall (l:: LocTy) (a:: LocTy) (b:: LocTy) (c :: LocTy) m. (KnownSymbol l, KnownSymbol a, KnownSymbol b, KnownSymbol c, Seq.MonadIO m) => 
                     (Proxy l, Async Int @ l) -> (Proxy a, Async Int @ a) ->  (Proxy b, Async Int @ b) ->  (Proxy c, Async Int @ c)  
        ->  Seq.StateT ((HashMap (String) NodeState), (HashMap (String) ( Int))) (Choreo m) ((HashMap (String) NodeState), (HashMap (String) ( Int)))
prepare (locl, req) (loca, msga) (locb, msgb) (locc, msgc) =  do
                   {-- Seq.lift (locl `locally` \un -> do  
                              Seq.liftIO $ putStrLn $ "prepare Leader:" ++ (show $ un req)
                              return ())
                    la <- Seq.lift ((locl, req) ~> loca)
                    lb <- Seq.lift ((locl, req) ~> locb)
                    lc <- Seq.lift ((locl, req) ~> locc)
                    updateState (proxyToString locl) --}
                    
                    reqa <- Seq.lift (loca `locally` \un -> do 
                              x <-  Seq.liftIO $ wait (un msga) 
                              Seq.liftIO $ putStrLn $ "prepare A:" ++ (show x)
                              return x )
                    al <- Seq.lift ((loca, reqa) ~> locl)
                    ab <- Seq.lift ((loca, reqa) ~> locb)
                    ac <- Seq.lift ((loca, reqa) ~> locc)
                    updateState (proxyToString loca) def

                    reqb <- Seq.lift (locb `locally` \un -> do 
                              x <-  Seq.liftIO $ wait (un msgb) 
                              Seq.liftIO $ putStrLn $ "prepare B:" ++ (show x)
                              return x )
                    bl <- Seq.lift ((locb, reqb) ~> locl)
                    ba <- Seq.lift ((locb, reqb) ~> loca)
                    bc <- Seq.lift ((locb, reqb) ~> locc)
                    updateState (proxyToString locb) def 

                    reqc <- Seq.lift (locc `locally` \un -> do 
                              x <-  Seq.liftIO $ wait (un msgc) 
                              Seq.liftIO $ putStrLn $ "prepare C:" ++ (show x)
                              return x )
                    cl <- Seq.lift ((locc, reqc) ~> locl)
                    ca <- Seq.lift ((locc, reqc) ~> loca)
                    cb <- Seq.lift ((locc, reqc) ~> locb)
                    updateState (proxyToString locc) def                           
                      >> commit (locl, [req, al, bl, cl]) (loca, [msga, ba, ca]) (locb, [msgb, ab, cb]) (locc, [msgc, ac, bc])

locOut :: forall a (loc ::LocTy). (KnownSymbol loc) => [a @ loc] -> [a] @ loc
locOut as = wrap (helperOut as)

helperOut :: forall a (loc ::LocTy). (KnownSymbol loc) => [a @ loc] -> [a]
helperOut (a:as) = (unwrap a) : (helperOut as)  

commit :: forall (l::LocTy) (a :: LocTy) (b :: LocTy) (c :: LocTy) m. 
          (KnownSymbol l, KnownSymbol a, KnownSymbol b, KnownSymbol c, Seq.MonadIO m) => 
          (Proxy l, [Async Int @ l]) -> (Proxy a, [Async Int @ a]) -> (Proxy b, [Async Int @ b]) -> (Proxy c, [Async Int @ c]) 
          ->  Seq.StateT ((HashMap (String) NodeState), (HashMap (String) (Int))) (Choreo m) ((HashMap (String) NodeState), (HashMap (String) (Int)))
commit  (locl, ls) (loca, as) (locb, bs) (locc, cs) =  do 
    let outl = locOut ls  
    repl <- Seq.lift (locl `locally` \un -> do 
                              x <-  Seq.liftIO (selecT $ compare_ (un outl) 2)
                              Seq.liftIO $ putStrLn $ "commit leader"
                              return x )
    updateState (proxyToString locl) def

    let outa = locOut as  
    repa <- Seq.lift (loca `locally` \un -> do 
                              x <-  Seq.liftIO (selecT $ compare_ (un outa) 2)
                              Seq.liftIO $ putStrLn $ "commit A"
                              return x )
    updateState (proxyToString loca) def

    let outb = locOut bs  
    repb <- Seq.lift (locb `locally` \un -> do 
                              x <-  Seq.liftIO ( selecT $ compare_ (un outb) 2 )
                              Seq.liftIO $ putStrLn $ "commit B"
                              return x )
    updateState (proxyToString locb) def

    let outc = locOut cs  
    repc <- Seq.lift (locc `locally` \un -> do 
                              x <-  Seq.liftIO (selecT $ compare_ (un outc) 2)
                              Seq.liftIO $ putStrLn $ "commit C"
                              return x )
    updateState (proxyToString locc) def
     >> reply (locl, repl) (loca, repa) (locb, repb) (locc, repc)

reply :: forall (l::LocTy) (a :: LocTy) (b :: LocTy) (c :: LocTy) m. 
          (KnownSymbol l, KnownSymbol a, KnownSymbol b, KnownSymbol c, Seq.MonadIO m) => 
          (Proxy l, Async Int @ l) -> (Proxy a, Async Int @ a) -> (Proxy b, Async Int @ b) -> (Proxy c, Async Int @ c)
          ->  Seq.StateT ((HashMap (String) NodeState), (HashMap (String) (Int))) (Choreo m) ((HashMap (String) NodeState), (HashMap (String) (Int)))
        --  -> Choreo IO ([Async Int] @ "client")
reply (locl, repl) (loca, repa) (locb, repb) (locc, repc) = do 
    repl' <-  Seq.lift (locl `locally` \un -> do 
                              x <- Seq.liftIO (wait (un repl))
                              Seq.liftIO $ putStrLn $ "reply leader"
                              if (x /= failVal) then (return $ times3 x) else return (failVal) )
    rl <-  Seq.lift $ (locl, repl') ~> client

    repa <- Seq.lift(loca `locally` \un -> do 
                              x <-  Seq.liftIO $ (wait $ un repa)
                              Seq.liftIO $ putStrLn $ "reply A"
                              if (x /= failVal) then (return $ times3 x) else return (failVal) )
    ra <-  Seq.lift $ (loca, repa) ~> client

    repb <- Seq.lift (locb `locally` \un -> do 
                               x <- Seq.liftIO $ (wait $ un repb)
                               Seq.liftIO $ putStrLn $ "reply B"
                               if (x /= failVal) then (return $ times3 x) else return (failVal) )
    rb <-  Seq.lift $ (locb, repb) ~> client

    repc <- Seq.lift (locc `locally` \un -> do 
                               x <-  Seq.liftIO $ (wait $ un repc)
                               Seq.liftIO $ putStrLn $ "reply C"
                               if (x /= failVal) then (return $ times3 x) else return (failVal) )
    rc <-  Seq.lift $ (locc, repc) ~> client

    let replies =  locOut [rl,ra,rb,rc]
    replies <- Seq.lift $ client `locally` \un -> do 
        answer <- Seq.liftIO $ selecT $ compare_ (un replies) 2
        finalans <- Seq.liftIO $ wait answer
        Seq.liftIO $ putStrLn $ "result at client:" ++ (show finalans)
    
    updateState (proxyToString locl) def
    updateState (proxyToString loca) def
    updateState (proxyToString locb) def
    updateState (proxyToString locc) def


pBFTMain :: HttpConfig -> IO ()
pBFTMain cfg = do
  [loc] <- getArgs
  void $ runChoreography cfg pbft loc  >> (pBFTMain cfg)
 
main = do 
  pBFTMain cfg 
 where
    cfg = mkHttpConfig [ ("A", ("localhost", 4242))
                       , ("B", ("localhost", 4343))
                       , ("C", ("localhost", 4544))
                       , ("leader", ("localhost", 4545))
                       , ("client", ("localhost", 4546))
                       ]
