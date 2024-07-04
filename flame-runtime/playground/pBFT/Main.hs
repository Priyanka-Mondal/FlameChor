{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PostfixOperators, TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -fplugin Flame.Solver -fobject-code #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Use const" #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# HLINT ignore "Redundant $" #-}
{-# HLINT ignore "Use let" #-}
 
module Main where

--import MyHasChor.Choreography
import MyHasChor.Choreography.Location
import MyHasChor.Choreography.NetworkAsync
import MyHasChor.Choreography.NetworkAsync.Http
import MyHasChor.Choreography.ChoreoAsync
import Control.Concurrent.Async
import Control.Monad.IO.Class
--import MyHasChor.Choreography.Flaqr
--import MyHasChor.Choreography.LabelledAsync
import System.Environment
import Data.Time
import Data.Maybe (isJust, fromJust)
import Data.Either (isLeft)
import System.Timeout 
import Data.Proxy
import Data.IORef
--import Control.Monad
import GHC.TypeLits
import Data.List hiding (compare)
import Data.Monoid (Last(getLast))
import GHC.Conc.IO (threadDelay)
import Prelude hiding (compare)
--import Choreography.ChoreoAsync (cond)
import Flame.Principals
import Flame.TCB.Freer.IFC

    ( type (!)(..),
      Labeled,
      bind,
      label,
      use,
      protect,
      join,
      restrict,
      runLabeled,
      relabel' )
import Flame.Assert
import GHC.TypeLits (KnownSymbol)
import Data.Text.Internal.Fusion.Types (CC)
import Data.Sequence (adjust')
import System.IO.Error (modifyIOError)
maybeToEither :: e -> Maybe a -> Either e a
maybeToEither e Nothing = Left e
maybeToEither _ (Just a) = Right a


type E = N "A"
locA :: SPrin E
locA = SName (Proxy :: Proxy "A")

type B = N "B"
locB :: SPrin B
locB = SName (Proxy :: Proxy "B")

type D = N "C"
locC :: SPrin D
locC = SName (Proxy :: Proxy "C")

type Client = N "client"
client :: SPrin Client
client = SName (Proxy :: Proxy "client")

type Leader = N "leader"
leader :: SPrin Leader
leader = SName (Proxy :: Proxy "leader")


type ABC = ((((E \/ B) \/ D) \/ Client ) \/ Leader)
   --deriving (Show)

abc :: SPrin ABC
abc = ((((locA *\/ locB) *\/ locC) *\/ client) *\/ leader)

type FromA = ABC 
fromA :: SPrin ABC
fromA = abc

type FromB = ABC 
fromB :: SPrin ABC
fromB = abc

type FromC = ABC 
fromC :: SPrin ABC
fromC = abc

type FromClient = ABC 
fromClient :: SPrin ABC
fromClient = abc

type FromLeader = ABC 
fromLeader :: SPrin ABC
fromLeader = abc

sPutStrLn :: Show a => SPrin pc -> (l ⊑ pc) => l!a -> Labeled IO pc (pc!())
sPutStrLn pc la = restrict pc (\open -> print (open la))

sGetLine :: SPrin pc -> Labeled IO pc (pc!Int)
sGetLine pc = restrict pc (\_ -> readLn)

strGetLine :: SPrin pc -> Labeled IO pc (pc!String)
strGetLine pc = restrict pc (\_ -> readLn)

safePutStrLn :: forall l a. (Show a, l ⊑ ABC) => l!a 
                      -> Labeled IO ABC (ABC!())
safePutStrLn =  sPutStrLn abc

safeNewIORef :: forall l a pc. (Show a, l ⊑ ABC) => a 
                      -> Labeled IO ABC (ABC!(IORef a))
safeNewIORef s =  restrict abc (\_ -> newIORef s)

safeReadIORef :: forall l a pc. (Show a, l ⊑ ABC) => 
                         l!IORef a
                      -> Labeled IO ABC (ABC!a)
safeReadIORef s =  restrict abc (\open -> readIORef (open s))

safeModifyIORef :: forall l a pc. (Show a, l ⊑ ABC) => 
                         l!IORef a ->(a->a)
                      -> Labeled IO ABC (ABC!())
safeModifyIORef s f = restrict abc (\open -> modifyIORef (open s) f)
--
--IORef State -> (State -> State) -> IO ()

aGetLine :: Labeled IO FromA (FromA ! Int)
aGetLine = sGetLine fromA

bGetLine :: Labeled IO FromB (FromB ! Int)
bGetLine = sGetLine fromB

cGetLine :: Labeled IO FromC (FromC ! Int)
cGetLine = sGetLine fromC

clientGetLine :: Labeled IO FromClient (FromClient!Int)
clientGetLine = sGetLine fromClient

leaderGetLine :: Labeled IO FromLeader (FromLeader!Int)
leaderGetLine = sGetLine fromLeader
--------------
--------------
instance Show a => Show (l ! a) where
  show (Seal x) = "Seal " ++ show x
instance Read a => Read (l ! a) where
  readsPrec _ s = [(Seal x, rest) | ("Seal", rest1) <- lex s, (x, rest) <- readsPrec 0 rest1]
instance Eq a => Eq (l ! a) where
  (Seal a) == (Seal b) = a == b

cond' :: (Show a, Read a, KnownSymbol l)
     => (Proxy l, a @ l)  -- ^ A pair of a location and a scrutinee located on
                          -- it.
     -> (a -> Choreo m b) -- ^ A function that describes the follow-up
                          -- choreographies based on the value of scrutinee.
     -> Choreo m b
cond' (l, a) c = undefined -- stub for type signature

labelInA :: l!(Async a @ loc) -> Async (l!a) @ loc
labelInA (Seal asl) = case asl of
                        Wrap as -> Wrap $ Prelude.fmap Seal as
                        Empty   -> Empty

labelIn :: l!(a @ loc) -> (l!a) @ loc
labelIn (Seal asl) = case asl of
                        Wrap as -> Wrap $ Seal as
                        Empty   -> Empty


labelInM :: Monad m => Labeled m pc (l!(a @ loc)) -> Labeled m pc ((l!a) @ loc)
labelInM e = labelIn <$> e

labelInMA :: Monad m => Labeled m pc (l!(Async a @ loc)) -> Labeled m pc (Async (l!a) @ loc)
labelInMA e = labelInA <$> e

labelOutA :: Async (l!a) @ loc -> l!(Async a @ loc)
labelOutA (Wrap as) = Seal (Wrap $ Prelude.fmap (\(Seal a) -> a) as)
labelOutA Empty     = Seal Empty

labelOut :: (l!a) @ loc -> l!(a @ loc)
labelOut (Wrap as) = Seal (Wrap $ (\(Seal a) -> a) as)
labelOut Empty     = Seal Empty

labelOutMA :: Labeled m pc (Async (l!a) @ loc) -> Labeled m pc (l!(Async a @ loc))
labelOutMA e = labelOutA <$> e

labelOutM :: Labeled m pc ((l!a) @ loc) -> Labeled m pc (l!(a @ loc))
labelOutM e = labelOut <$> e

joinLoc :: forall l l' l'' loc a. (l ⊑ l'', l' ⊑ l'') => (l!(l'!a)) @ loc -> (l''!a) @ loc
joinLoc (Wrap lla) = Wrap $ join lla
joinLoc Empty      = Empty

sLocally :: forall pc loc_pc l loc m a. (Monad m, KnownSymbol loc, pc ⊑ loc_pc, pc ⊑ l)
               => (SPrin pc, SPrin (N loc), SPrin loc_pc, SPrin l)
               -> (Unwrap loc -> Labeled m loc_pc (l!a))
               -> Labeled (Choreo m) pc ((l!a) @ loc)
sLocally (pc, loc, loc_pc, l) k = do
  result <- restrict pc (\_ -> locally (sym loc) (\un -> runLabeled $ k un))
  return $ joinLoc (labelIn result)

(~>:) :: (Show a, Read a, KnownSymbol loc, KnownSymbol loc') --, (N loc') ≽ (C pc), (N loc) ≽ (I pc))
     => (Proxy loc, SPrin pc, SPrin l, (l!a) @ loc)  -- ^ A triple of a sender's location, a clearance, 
                                           -- and a value located
                                           -- at the sender
     -> Proxy loc'                           -- ^ A receiver's location.
     -> Labeled (Choreo m) pc (Async (pc!(l!a)) @ loc')
(~>:) (loc, pc, l, la) loc' = do
  result <- restrict pc (\_ -> (loc, la) ~> loc')
  return $ labelInA result
-- ab <- (client, abc, fromClient) `ccompare` a' b'

data Failed = Fail
class CanFail m where
  ready  :: m a -> IO Bool -- do we ever want a non-IO effect?
  failed :: m a -> IO Bool
  force  :: m a -> IO (Either Failed a)
  forceEither :: m a -> m b -> IO (Either (Either Failed a) (Either Failed b))

  -- | Blocks until force completes or timeout is reached
  forceUntil :: Int -> m a -> IO (Either Failed a)
  forceUntil n a = timeout n (force a) >>= \case 
                     Just (Right a) -> return $ Right a
                     _ -> return $ Left Fail

  -- | Blocks until force on a or b completes or timeout is reached.
  forceEitherUntil :: Int -> m a -> m b -> IO (Either (Either Failed a) (Either Failed b))
  forceEitherUntil n a b = timeout n (forceEither a b) >>= \case 
                     Just (Left ea) -> return $ Left ea
                     Just (Right eb) -> return $ Right eb
                     Nothing -> return $ Left (Left Fail)

eitherToCanFail :: Either e a -> Either Failed a
eitherToCanFail = either (const $ Left Fail) Right

instance (CanFail Async) where
  -- | Returns true if Async has completed (successfully or not)
  ready a = poll a >>= \r -> return $ isJust r
  -- | Returns true if Async has completed with an exception
  failed a = poll a >>= \r -> return (isJust r && isLeft (fromJust r))

  -- | Blocks until Async completes 
  force a = waitCatch a >>= \case
    Left exc -> return $ Left Fail
    Right a'' -> return $ Right a''

  -- | Blocks until Async completes 
  forceEither a b = waitEitherCatch a b >>= \case
      Left ea  -> return $ (Left  . eitherToCanFail) ea
      Right eb -> return $ (Right . eitherToCanFail) eb
  
timeOut :: Int 
timeOut = 10000000
instance (CanFail (Either Failed)) where
  ready a = return True
  failed = return . isLeft
  force = return
  forceEither a b = do 
    case a of
      Left ea -> case b of 
        Left eb -> return $ (Right (Left Fail)) -- ?? Left (Left Fail)
        Right b' -> return $ Right (Right b') --(Right . eitherToCanFail) b
      Right a' -> return $ Left (Right a') --(Right . eitherToCanFail) b

sSelect :: forall l1 l2 m m' a. (CanFail m, Eq a) => m (l1!a) -> m (l2!a)
  -> IO (Either Failed ((C (l1 ⊔ l2) ∧ I(l1 ∨ l2) ∧ A(l1 ∧ l2))!a))
sSelect a b = do 
  forceEitherUntil timeOut a b >>= \case
      Right (Left Fail) -> return $ Left Fail
      Left (Left Fail) -> return $ Left Fail
      Left (Right (Seal a')) -> return $ Right (Seal a')
      Right (Right (Seal b')) -> return $ Right (Seal b')

sSelect' :: forall l1 l2 m m' a pc. (CanFail m, Eq a, pc ⊑ l1, pc ⊑ l2) => (SPrin pc)
  -> Labeled IO pc (m (l1!a)) 
  -> Labeled IO pc (m (l2!a))
  -> Labeled IO pc (pc!(Either Failed ((C (l1 ⊔ l2) ∧ I(l1 ∨ l2) ∧ A(l1 ∧ l2))!a)))
sSelect' pc a' b' = do
  a <- a'
  b <- b'  
  restrict pc (\_ ->
    liftIO $ forceEitherUntil timeOut a b >>= \case
        Right (Left Fail) -> return $ Left Fail
        Left (Left Fail) -> return $ Left Fail
        Left (Right (Seal a')) -> return $ Right (Seal a')
        Right (Right (Seal b')) -> return $ Right (Seal b')
        )

sSelect'' :: forall l1 l2 m m' a pc. (CanFail m, Eq a, pc ⊑ l1, pc ⊑ l2) => 
   IO (m (l1!a)) 
  -> IO (m (l2!a))
  -> IO ((Either Failed ((C (l1 ⊔ l2) ∧ I(l1 ∨ l2) ∧ A(l1 ∧ l2))!a)))
sSelect'' a' b' = do
  a <- a'
  b <- b'  
  forceEitherUntil timeOut a b >>= \case
        Right (Left Fail) -> return $ Left Fail
        Left (Left Fail) -> return $ Left Fail
        Left (Right (Seal a')) -> return $ Right (Seal a')
        Right (Right (Seal b')) -> return $ Right (Seal b')


sCompare :: forall l1 l2 m m' a. (CanFail m, Eq a) => m (l1!a) -> m (l2!a)
  -> IO (Either Failed ((C (l1 ⊔ l2) ∧ I(l1 ∧ l2) ∧ A(l1 ∨ l2))!a))
sCompare a b = 
  forceEitherUntil timeOut a b >>= \case
    Left (Left Fail) -> return (Left Fail)
    Left (Right (Seal a')) -> 
      forceUntil timeOut b >>= \case 
        Left Fail -> return $ Left Fail
        Right (Seal b') -> return $ if a' == b' then Right (Seal a') else Left Fail

    Right (Left Fail) -> return (Left Fail)
    Right (Right (Seal b')) -> 
      forceUntil timeOut a >>= \case 
        Left Fail -> return $ Left Fail
        Right (Seal a') -> return $ if a' == b' then Right (Seal b') else Left Fail

sCompare' :: forall l1 l2 m a pc. (CanFail m, Eq a, pc ⊑ l1, pc ⊑ l2) => (SPrin pc)
  -> Labeled IO pc (m (l1!a)) 
  -> Labeled IO pc (m (l2!a))
  -> Labeled IO pc (pc!(Either Failed ((C (l1 ⊔ l2) ∧ I(l1 ∧ l2) ∧ A(l1 ∨ l2))!a)))
sCompare' pc a' b' = do
  a <- a'
  b <- b'
  restrict pc (\_ -> 
      liftIO $ forceEitherUntil timeOut a b >>= \case
        Left (Left Fail) -> return (Left Fail)
        Left (Right (Seal a')) -> 
           liftIO $ forceUntil timeOut b >>= \case 
            Left Fail -> return $ Left Fail
            Right (Seal b') -> return $ if a' == b' then Right (Seal a') else Left Fail

        Right (Left Fail) -> return (Left Fail)
        Right (Right (Seal b')) -> 
           liftIO $ forceUntil timeOut a >>= \case 
            Left Fail -> return $ Left Fail
            Right (Seal a') -> return $ if a' == b' then Right (Seal b') else Left Fail
    )

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

pbft :: Labeled (Choreo IO) ABC () --ABC ((ABC ! ())  @ "client") --forall (a:: LocTy). (KnownSymbol a) => Seq.StateT (SystemState a) IO NodeState --Choreo IO ()
pbft = do 
  locAState <- (abc, locA, abc, fromA) `sLocally` \_ -> safeNewIORef ("INIT" :: State)
  locBState <- (abc, locB, abc, fromB) `sLocally` \_ -> safeNewIORef ("INIT" :: State)
  locCState <- (abc, locC, abc, fromC) `sLocally` \_ -> safeNewIORef ("INIT" :: State)
  locLState <- (abc, leader, abc, fromLeader) `sLocally` \_ -> safeNewIORef ("INIT" :: State)
 
  request <- (abc, client, abc, fromClient) `sLocally` \_ -> do
      safePutStrLn @ABC $ label "Client$ Input:"
      relabel' abc clientGetLine
  
  req <- (sym client, abc, fromClient, request) ~>: sym leader 

  --preprepare 
  (ppa, ppb, ppc) <- preprepare (req, locLState)
  (pl, pa, pb, pc) <- prepare (ppa, ppb, ppc, locLState, locAState, locBState, locCState)
  --commit ((locLState, pl), (locAState, pa), (locBState, pb), (locCState, pc))
 
 
  return ()
  

  {-  

  (repl, repa, repb, repc) <- commit (leader, locLState, ml) (locA, locAState, ma) (locB, locBState, mb) (locC, locCState, mc)
  reply(leader, locLState, repl) (locA, locAState, repa) (locB, locBState, repb) (locC, locCState, repc)

  return () 
-}
preprepare :: (Async (ABC ! (ABC ! Int)) @ "leader", (ABC ! IORef State) @ "leader")
                  -> Labeled (Choreo IO) ABC ((Async (ABC ! (ABC ! Int)) @ "A", 
                  Async(ABC ! (ABC ! Int)) @ "B", 
                  Async (ABC ! (ABC ! Int)) @ "C"))
preprepare (req, statel) =  do
                           req' <- (abc, leader, abc, fromLeader) `sLocally` \un -> do  
                             x <- return $ un req
                             let z' = join @_ @_ @ABC <$> wait x
                             x' <- (join @_ @_ @ABC <$> restrict abc (\_-> z'))
                             safePutStrLn @ABC $ label $ "preprepare leader:" ++ show x'
                             safeModifyIORef (un statel) nextState
                             return x'
                           prepa <-  (sym leader, abc, fromLeader, req') ~>: sym locA
                           prepb <-  (sym leader, abc, fromLeader, req') ~>: sym locB  
                           prepc <-  (sym leader, abc, fromLeader, req') ~>: sym locC
                           return $ (prepa, prepb, prepc)

prepare ::  ((Async (ABC ! (ABC ! Int)) @ "A", Async (ABC ! (ABC ! Int)) @ "B",
            Async (ABC ! (ABC ! Int)) @ "C", (ABC ! IORef State) @ "leader",
              (ABC ! IORef State) @ "A", (ABC ! IORef State) @ "B",
              (ABC ! IORef State) @ "C")) -> 
              Labeled (Choreo IO) ABC ((ABC ! [Async (ABC ! (ABC ! Int))]) @ "leader", 
              (ABC ! [Async (ABC ! (ABC ! Int))]) @ "A", (ABC ! [Async (ABC ! (ABC ! Int))]) @ "B", 
              (ABC ! [Async (ABC ! (ABC ! Int))]) @ "C")
prepare (ppa, ppb, ppc, statel, statea, stateb, statec) =  do
        reqa <- (abc, locA, abc, fromA) `sLocally` \un -> do  
                  x <- return $ un ppa
                  let z' = join @_ @_ @ABC <$> wait x
                  x' <- (join @_ @_ @ABC <$> restrict abc (\_-> z'))
                  safePutStrLn @ABC $ label $ "prepare A:" ++ show x'
                  safeModifyIORef (un statea) nextState
                  return x'
        al <- (sym locA, abc, fromA, reqa) ~>: sym leader
        ab <- (sym locA, abc, fromA, reqa) ~>: sym locB
        ac <- (sym locA, abc, fromA, reqa) ~>: sym locC

        reqb <- (abc, locB, abc, fromB) `sLocally` \un -> do  
                  x <- return $ un ppb
                  let z' = join @_ @_ @ABC <$> wait x
                  x' <- (join @_ @_ @ABC <$> restrict abc (\_-> z'))
                  safePutStrLn @ABC $ label $ "prepare B:" ++ show x'
                  safeModifyIORef (un stateb) nextState
                  return x'
        bl <- (sym locB, abc, fromB, reqb) ~>: sym leader
        ba <- (sym locB, abc, fromB, reqb) ~>: sym locA
        bc <- (sym locB, abc, fromB, reqb) ~>: sym locC
      
        reqc <- (abc, locC, abc, fromC) `sLocally` \un -> do  
                  x <- return $ un ppc
                  let z' = join @_ @_ @ABC <$> wait x
                  x' <- (join @_ @_ @ABC <$> restrict abc (\_-> z'))
                  safePutStrLn @ABC $ label $ "prepare C:" ++ show x'
                  safeModifyIORef (un statec) nextState
                  return x'
        cl <- (sym locC, abc, fromC, reqc) ~>: sym leader
        ca <- (sym locC, abc, fromC, reqc) ~>: sym locA
        cb <- (sym locC, abc, fromC, reqc) ~>: sym locB
---------------------------------COMMIT------------------------------------------------------------------
-- al bl and cl 

        repl <-  (abc, leader, abc, fromLeader) `sLocally` \un -> do 
            ab <- (sCompare' abc (return (un al)) (return (un bl))) 
            bc <- (sCompare' abc (return (un bl)) (return (un cl)))
            ca <- (sCompare' abc (return (un cl)) (return (un al)))
            abbc <- use ab (\ab' -> (use bc (\bc' -> sSelect' abc (return ab') (return bc'))))
            use @_ @ABC @ABC abbc (\abbc' -> use ca (\ca'-> sSelect' abc (return abbc') (return ca')))   
            y <- safeReadIORef $ un statel
            if y == Seal "PREPREPARE" then 
              do
                safeModifyIORef (un statel) nextState 
                safePutStrLn $ label "commit leader:"  -- ++ un statel
                return abbc 
              else 
              do 
                init <- safeNewIORef ("INIT" :: State)
                safeModifyIORef init nextState 
                return $ label $ Left Fail

        repa <-  (abc, locA, abc, fromA) `sLocally` \un -> do 
            ab <- (sCompare' abc (return (un ppa)) (return (un ba))) 
            bc <- (sCompare' abc (return (un ba)) (return (un ca)))
            ca <- (sCompare' abc (return (un ca)) (return (un ppa)))
            abbc <- use ab (\ab' -> (use bc (\bc' -> sSelect' abc (return ab') (return bc'))))
            use @_ @ABC @ABC abbc (\abbc' -> use ca (\ca'-> sSelect' abc (return abbc') (return ca')))   
            y <- safeReadIORef $ un statea
            if y == Seal "PREPREPARE" then 
              do
                safeModifyIORef (un statea) nextState 
                safePutStrLn $ label "commit A:"  -- ++ un statel
                return abbc 
              else 
              do 
                init <- safeNewIORef ("INIT" :: State)
                safeModifyIORef init nextState 
                return $ label $ Left Fail

        repb <-  (abc, locB, abc, fromB) `sLocally` \un -> do 
            ab' <- (sCompare' abc (return (un ppb)) (return (un ab))) 
            bc <- (sCompare' abc (return (un ab)) (return (un cb)))
            ca <- (sCompare' abc (return (un cb)) (return (un ppb)))
            abbc <- use ab' (\ab' -> (use bc (\bc' -> sSelect' abc (return ab') (return bc'))))
            use @_ @ABC @ABC abbc (\abbc' -> use ca (\ca'-> sSelect' abc (return abbc') (return ca')))   
            y <- safeReadIORef $ un stateb
            if y == Seal "PREPREPARE" then 
              do
                safeModifyIORef (un stateb) nextState 
                safePutStrLn $ label "commit B:"  -- ++ un statel
                return abbc 
              else 
              do 
                init <- safeNewIORef ("INIT" :: State)
                safeModifyIORef init nextState 
                return $ label $ Left Fail

        repc <-  (abc, locC, abc, fromC) `sLocally` \un -> do 
            ab' <- (sCompare' abc (return (un ppc)) (return (un ac))) 
            bc' <- (sCompare' abc (return (un ac)) (return (un bc)))
            ca <- (sCompare' abc (return (un bc)) (return (un ppc)))
            abbc <- use ab' (\ab' -> (use bc' (\bc' -> sSelect' abc (return ab') (return bc'))))
            use @_ @ABC @ABC abbc (\abbc' -> use ca (\ca'-> sSelect' abc (return abbc') (return ca')))   
            y <- safeReadIORef $ un statec
            if y == Seal "PREPREPARE" then 
              do
                safeModifyIORef (un statec) nextState 
                safePutStrLn $ label "commit C:"  -- ++ un statel
                return abbc 
              else 
              do 
                init <- safeNewIORef ("INIT" :: State)
                safeModifyIORef init nextState 
                return $ label $ Left Fail


        retl <- (abc, leader, abc, fromLeader) `sLocally` \un -> return $ label [un al, un bl, un cl]
        reta <- (abc, locA, abc, fromA) `sLocally` \un -> return $ label [un ba, un ca]
        retb <- (abc, locB, abc, fromB) `sLocally` \un -> return $ label  [un ab, un cb]
        retc <- (abc, locC, abc, fromC) `sLocally` \un -> return $ label [un ac, un bc]
        return (retl, reta, retb, retc) 
                  
{-
commit :: forall (l::LocTy) (a :: LocTy) (b :: LocTy) (c :: LocTy). 
          (KnownSymbol l, KnownSymbol a, KnownSymbol b, KnownSymbol c) => 
             (Proxy l, IORef State @ l, [Async Int] @ l) 
          -> (Proxy a, IORef State @ a, [Async Int] @ a) 
          -> (Proxy b, IORef State @ b, [Async Int] @ b) 
          -> (Proxy c, IORef State @ c, [Async Int] @ c) 
          -> Choreo IO (Async Int @ l, Async Int @ a, Async Int @ b, Async Int @ c)
commit  (locl, statel, ls) (loca, statea, as) (locb, stateb, bs) (locc, statec, cs) =  do 
    --let outl = locOut ls  
    repl <- locl `locally` \un -> do 
                              x <-  selecT $ compare_ (un ls) 2
                              y <- readIORef $ un statel
                              if y == "PREPREPARE" then 
                                do
                                  modifyIORef (un statel) nextState 
                                  putStrLn "commit leader:"  -- ++ un statel
                                  return x 
                               else 
                                do 
                                  init <- newioref
                                  modifyIORef init nextState 
                                  async $ return failVal
    
    --let outa = locOut as  
    repa <- loca `locally` \un -> do 
                              x <- selecT $ compare_ (un as) 2
                              y <- readIORef $ un statea
                              if y == "PREPREPARE" then 
                                do
                                  modifyIORef (un statea) nextState 
                                  putStrLn "commit A:" -- ++ un statel
                                  return x 
                               else 
                                do 
                                  print y
                                  init <- newioref
                                  modifyIORef init nextState 
                                  async $ return failVal
    
    --let outb = locOut bs  
    repb <- locb `locally` \un -> do 
                              x <-   selecT $ compare_ (un bs) 2 
                              y <- readIORef $ un stateb
                              if y == "PREPREPARE" then 
                                do
                                  modifyIORef (un stateb) nextState 
                                  putStrLn "commit B:" -- ++ un statel
                                  return x 
                               else 
                                do 
                                  init <- newioref
                                  modifyIORef init nextState 
                                  async $ return failVal
  
    --let outc = locOut cs  
    repc <- locc `locally` \un -> do 
                              x <-  selecT $ compare_ (un cs) 2
                              y <- readIORef $ un statec
                              if y == "PREPREPARE" then 
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

-}
{-                
commit :: forall (l::LocTy) (a :: LocTy) (b :: LocTy) (c :: LocTy). 
          (KnownSymbol l, KnownSymbol a, KnownSymbol b, KnownSymbol c) => 
             (Proxy l, IORef State @ l, [Async Int] @ l) 
          -> (Proxy a, IORef State @ a, [Async Int] @ a) 
          -> (Proxy b, IORef State @ b, [Async Int] @ b) 
          -> (Proxy c, IORef State @ c, [Async Int] @ c) 
          -> Choreo IO (Async Int @ l, Async Int @ a, Async Int @ b, Async Int @ c)
commit  (locl, statel, ls) (loca, statea, as) (locb, stateb, bs) (locc, statec, cs) =  do 
    --let outl = locOut ls  
    repl <- locl `locally` \un -> do 
                              x <-  selecT $ compare_ (un ls) 2
                              y <- readIORef $ un statel
                              if y == "PREPREPARE" then 
                                do
                                  modifyIORef (un statel) nextState 
                                  putStrLn "commit leader:"  -- ++ un statel
                                  return x 
                               else 
                                do 
                                  init <- newioref
                                  modifyIORef init nextState 
                                  async $ return failVal
    
    --let outa = locOut as  
    repa <- loca `locally` \un -> do 
                              x <- selecT $ compare_ (un as) 2
                              y <- readIORef $ un statea
                              if y == "PREPREPARE" then 
                                do
                                  modifyIORef (un statea) nextState 
                                  putStrLn "commit A:" -- ++ un statel
                                  return x 
                               else 
                                do 
                                  print y
                                  init <- newioref
                                  modifyIORef init nextState 
                                  async $ return failVal
    
    --let outb = locOut bs  
    repb <- locb `locally` \un -> do 
                              x <-   selecT $ compare_ (un bs) 2 
                              y <- readIORef $ un stateb
                              if y == "PREPREPARE" then 
                                do
                                  modifyIORef (un stateb) nextState 
                                  putStrLn "commit B:" -- ++ un statel
                                  return x 
                               else 
                                do 
                                  init <- newioref
                                  modifyIORef init nextState 
                                  async $ return failVal
  
    --let outc = locOut cs  
    repc <- locc `locally` \un -> do 
                              x <-  selecT $ compare_ (un cs) 2
                              y <- readIORef $ un statec
                              if y == "PREPREPARE" then 
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
                              putStrLn $ "reply leader:" ++ show (times3 x) -- ++ un statea
                              if x /= failVal then return $ times3 x else return failVal 
    rl <-  (locl, repl') ~> client

    repa <- loca `locally` \un -> do 
                              x <-  wait $ un repa
                              modifyIORef (un statea) nextState
                              putStrLn $ "reply A:" ++ show (times3 x) -- ++ un statea
                              if x /= failVal then return $ times3 x else return failVal
    ra <- (loca, repa) ~> client

    repb <- locb `locally` \un -> do 
                               x <- wait $ un repb
                               modifyIORef (un stateb) nextState
                               putStrLn $ "reply B:" ++ show (times3 x) 
                               if x /= failVal then return $ times3 x else return failVal
    rb <- (locb, repb) ~> client

    repc <- locc `locally` \un -> do 
                               x <- wait $ un repc
                               modifyIORef (un statec) nextState
                               putStrLn $ "reply C:" ++ show (times3 x) 
                               if x /= failVal then return $ times3 x else return failVal 
    rc <-  (locc, repc) ~> client

    --let replies =  locOut [rl,ra,rb,rc] -- [x @ loc] --> [x] @ loc
    replies <- client `locally` \un -> do 
        let replies = [un rl, un ra, un rb, un rc]
        answer <- selecT $ compare_ replies 3
        finalans <- wait answer
        putStrLn $ "result at client:" ++ show finalans
    return ()
    
-}

pBFTMain :: HttpConfig -> IO ()
pBFTMain cfg = do
  [loc] <- getArgs
  runChoreography cfg (runLabeled pbft) loc  >> pBFTMain cfg
 
main = do 
  pBFTMain cfg 
 where
    cfg = mkHttpConfig [ ("A", ("localhost", 4242))
                       , ("B", ("localhost", 4343))
                       , ("C", ("localhost", 4544))
                       , ("leader", ("localhost", 4545))
                       , ("client", ("localhost", 4546))
                       ]
