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

times3 :: Int -> Int
times3 x =  x*3 

--type State = String  

iNIT :: String
iNIT = "INIT"

pREPREPARE :: String
pREPREPARE = "PREPREPARE"

pREPARE :: String
pREPARE = "PREPARE"

cOMMIT :: String
cOMMIT = "COMMIT"

type State = String
-- data State = INIT | PREPREPARE | PREPARE | COMMIT

{--nextState :: State -> State
nextState iNIT = pREPREPARE
nextState pREPREPARE = pREPARE
nextState pREPARE = cOMMIT
nextState cOMMIT = iNIT
nextState _ = iNIT
--}

nextState :: State -> State
nextState "INIT" = "PREPREPARE"
nextState "PREPREPARE" = "PREPARE"
nextState "PREPARE" = "COMMIT"
nextState "COMMIT" = "INIT"
nextState _ = "INIT"

locOut :: forall a (loc ::LocTy). (KnownSymbol loc) => [a @ loc] -> [a] @ loc
locOut as = wrap (helperOut as)

helperOut :: forall a (loc ::LocTy). (KnownSymbol loc) => [a @ loc] -> [a]
helperOut (a:as) = map unwrap as --a : helperOut as  


newioref :: IO (IORef State )
newioref = newIORef ("INIT" :: State)

pbft :: Choreo IO () --forall (a:: LocTy). (KnownSymbol a) => Seq.StateT (SystemState a) IO NodeState --Choreo IO ()
pbft = do 
  locAState <- locA `locally` \_ -> newIORef ("INIT" :: State)
  locBState <- locB `locally` \_ -> newIORef ("INIT" :: State)
  locCState <- locC `locally` \_ -> newIORef ("INIT" :: State)
  locLState <- leader `locally` \_ -> newIORef ("INIT" :: State)

  request <- client `locally` \_ -> do
      putStrLn "Client$ Input:"
      readLn :: IO Int
  
  req <- (client, request) ~> leader
  (prepa, prepb, prepc) <- preprepare (req, leader, locLState, locA, locAState, locB, locBState, locC, locCState)
  (ml, ma, mb, mc) <- prepare (leader, locLState, req) (locA, locAState, prepa) (locB, locBState, prepb) (locC, locCState, prepc) 
  (repl, repa, repb, repc) <- commit (leader, locLState, ml) (locA, locAState, ma) (locB, locBState, mb) (locC, locCState, mc)
  reply(leader, locLState, repl) (locA, locAState, repa) (locB, locBState, repb) (locC, locCState, repc)

  return () 

preprepare :: forall (a:: LocTy) (b:: LocTy) (c :: LocTy) (l :: LocTy) m. 
 (KnownSymbol a, KnownSymbol b, KnownSymbol c, KnownSymbol l) => 
                     (Async Int @ l, Proxy l, IORef State @ l, Proxy a, IORef State @ a,
                      Proxy b, IORef State @ b, Proxy c, IORef State @ c) 
                  -> Choreo IO (Async Int @ a, Async Int @ b, Async Int @ c)
preprepare (req, locl, statel, loca, statea, locb, stateb, locc, statec) =  do
                           req' <- locl `locally` \un -> do  
                            x <- wait (un req)  
                            modifyIORef (un statel) nextState 
                            return x
                           prepa <-  (locl,req') ~> loca
                           prepb <-  (locl, req') ~> locb  
                           prepc <-  (locl, req') ~> locc
                           return (prepa, prepb, prepc)

prepare :: forall (l :: LocTy) (a:: LocTy) (b:: LocTy) (c :: LocTy) m. (KnownSymbol l, KnownSymbol a, KnownSymbol b, KnownSymbol c) => 
         (Proxy l, IORef State @ l, Async Int @ l)  
      ->    (Proxy a, IORef State @ a, Async Int @ a) 
      ->  (Proxy b, IORef State @ b ,Async Int @ b) 
      ->  (Proxy c, IORef State @ c, Async Int @ c)  
      ->  Choreo IO ([Async Int @ l], [Async Int @ a], [Async Int @ b], [Async Int @ c])
prepare (locl, statel, req) (loca, statea, msga) (locb, stateb, msgb) (locc, statec, msgc) =  do
                    reqa <-  loca `locally` \un -> do 
                              x <-  wait (un msga) 
                              modifyIORef (un statea) nextState 
                              putStrLn $ "prepare A:" ++ show x
                              return x 
                    al <- (loca, reqa) ~> locl
                    ab <- (loca, reqa) ~> locb
                    ac <- (loca, reqa) ~> locc
    
                    reqb <- locb `locally` \un -> do 
                              x <- wait (un msgb) 
                              modifyIORef (un stateb) nextState 
                              putStrLn $ "prepare B:" ++ show x
                              return x 
                    bl <- (locb, reqb) ~> locl
                    ba <- (locb, reqb) ~> loca
                    bc <- (locb, reqb) ~> locc
                  
                    reqc <- locc `locally` \un -> do 
                              x <- wait (un msgc) 
                              modifyIORef (un statec) nextState 
                              putStrLn $ "prepare C:" ++ show x
                              return x
                    cl <- (locc, reqc) ~> locl
                    ca <- (locc, reqc) ~> loca
                    cb <- (locc, reqc) ~> locb 
                    
                    retl <- locl `locally` \un -> return [req, al, bl, cl]

                    return ([req, al, bl, cl], [msga, ba, ca], [msgb, ab, cb], [msgc, ac, bc])
                
                  
commit :: forall (l::LocTy) (a :: LocTy) (b :: LocTy) (c :: LocTy). 
          (KnownSymbol l, KnownSymbol a, KnownSymbol b, KnownSymbol c) => 
             (Proxy l, IORef State @ l, [Async Int @ l]) 
          -> (Proxy a, IORef State @ a, [Async Int @ a]) 
          -> (Proxy b, IORef State @ b, [Async Int @ b]) 
          -> (Proxy c, IORef State @ c, [Async Int @ c]) 
          -> Choreo IO (Async Int @ l, Async Int @ a, Async Int @ b, Async Int @ c)
commit  (locl, statel, ls) (loca, statea, as) (locb, stateb, bs) (locc, statec, cs) =  do 
    let outl = locOut ls  
    repl <- locl `locally` \un -> do 
                              x <-  selecT $ compare_ (un outl) 2
                              y <- readIORef $ un statel
                              if y == "PREPARE" then 
                                do
                                  modifyIORef (un statel) nextState 
                                  putStrLn "commit leader:" -- ++ un statel
                                  return x 
                               else 
                                do 
                                  init <- newioref
                                  modifyIORef init nextState 
                                  async $ return failVal
    
    let outa = locOut as  
    repa <- loca `locally` \un -> do 
                              x <- selecT $ compare_ (un outa) 2
                              y <- readIORef $ un statea
                              if y == "PREPARE" then 
                                do
                                  modifyIORef (un statea) nextState 
                                  putStrLn "commit A:" -- ++ un statel
                                  return x 
                               else 
                                do 
                                  init <- newioref
                                  modifyIORef init nextState 
                                  async $ return failVal
    
    let outb = locOut bs  
    repb <- locb `locally` \un -> do 
                              x <-   selecT $ compare_ (un outb) 2 
                              y <- readIORef $ un stateb
                              if y == "PREPARE" then 
                                do
                                  modifyIORef (un stateb) nextState 
                                  putStrLn "commit B:" -- ++ un statel
                                  return x 
                               else 
                                do 
                                  init <- newioref
                                  modifyIORef init nextState 
                                  async $ return failVal
  
    let outc = locOut cs  
    repc <- locc `locally` \un -> do 
                              x <-  selecT $ compare_ (un outc) 2
                              y <- readIORef $ un statec
                              if y == "PREPARE" then 
                                do
                                  modifyIORef (un statec) nextState 
                                  putStrLn "commit C:" -- ++ un statel
                                  return x 
                               else 
                                do 
                                  init <- newioref
                                  modifyIORef init nextState 
                                  async $ return failVal

    return (repl, repa, repb, repc)


reply :: forall (l::LocTy) (a :: LocTy) (b :: LocTy) (c :: LocTy). 
          (KnownSymbol l, KnownSymbol a, KnownSymbol b, KnownSymbol c) => 
          (Proxy l, IORef State @ l, Async Int @ l) 
       -> (Proxy a, IORef State @ a, Async Int @ a) 
       -> (Proxy b, IORef State @ b, Async Int @ b) 
       -> (Proxy c, IORef State @ c, Async Int @ c)
       -> Choreo IO ()
reply (locl, statel, repl) (loca, statea, repa) (locb, stateb, repb) (locc, statec, repc) = do 
    repl' <- locl `locally` \un -> do 
                              x <- wait (un repl)
                              modifyIORef (un statel) nextState
                              putStrLn "reply leader:" -- ++ show $ un statel
                              if x /= failVal then return $ times3 x else return failVal 
    rl <-  (locl, repl') ~> client

    repa <- loca `locally` \un -> do 
                              x <-  wait $ un repa
                              modifyIORef (un statea) nextState
                              putStrLn "reply A:" -- ++ un statea
                              if x /= failVal then return $ times3 x else return failVal
    ra <- (loca, repa) ~> client

    repb <- locb `locally` \un -> do 
                               x <- wait $ un repb
                               modifyIORef (un stateb) nextState
                               putStrLn "reply B:" -- ++ un stateb
                               if x /= failVal then return $ times3 x else return failVal
    rb <- (locb, repb) ~> client

    repc <- locc `locally` \un -> do 
                               x <- wait $ un repc
                               modifyIORef (un statec) nextState
                               putStrLn "reply C:" -- ++ un statec
                               if x /= failVal then return $ times3 x else return failVal 
    rc <-  (locc, repc) ~> client

    let replies =  locOut [rl,ra,rb,rc] -- [x @ loc] --> [x] @ loc
    replies <- client `locally` \un -> do 
        answer <- selecT $ compare_ (un replies) 2
        finalans <- wait answer
        putStrLn $ "result at client:" ++ show finalans
    return ()
    


pBFTMain :: HttpConfig -> IO ()
pBFTMain cfg = do
  [loc] <- getArgs
  void $ runChoreography cfg pbft loc  >> pBFTMain cfg
 
main = do 
  pBFTMain cfg 
 where
    cfg = mkHttpConfig [ ("A", ("localhost", 4242))
                       , ("B", ("localhost", 4343))
                       , ("C", ("localhost", 4544))
                       , ("leader", ("localhost", 4545))
                       , ("client", ("localhost", 4546))
                       ]
