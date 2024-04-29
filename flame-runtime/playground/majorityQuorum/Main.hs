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
--{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "[Replace {rtype = Expr, pos = SrcSpan {startLine = 132, startCol = 57, endLine = 132, endCol = 81}, subts = [("a",SrcSpan {startLine = 132, startCol = 64, endLine = 132, endCol = 74}),("b",SrcSpan {startLine = 132, startCol = 77, endLine = 132, endCol = 78})], orig = "a . b"}]" #-}


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


type ABC = (((E \/ B) \/ D) \/ Client )
   --deriving (Show)

abc :: SPrin ABC
abc = (((locA *\/ locB) *\/ locC) *\/ client)

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

sPutStrLn :: Show a => SPrin pc -> (l ⊑ pc) => l!a -> Labeled IO pc (pc!())
sPutStrLn pc la = restrict pc (\open -> print (open la))

sGetLine :: SPrin pc -> Labeled IO pc (pc!Int)
sGetLine pc = restrict pc (\_ -> readLn)

strGetLine :: SPrin pc -> Labeled IO pc (pc!String)
strGetLine pc = restrict pc (\_ -> readLn)

safePutStrLn :: forall l a. (Show a, l ⊑ ABC) => l!a 
                      -> Labeled IO ABC (ABC!())
safePutStrLn =  sPutStrLn  abc

aGetLine :: Labeled IO FromA (FromA ! Int)
aGetLine = sGetLine fromA

bGetLine :: Labeled IO FromB (FromB ! Int)
bGetLine = sGetLine fromB

cGetLine :: Labeled IO FromC (FromC ! Int)
cGetLine = sGetLine fromC

clientGetLine :: Labeled IO FromClient (FromClient!Int)
clientGetLine = sGetLine fromClient
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
  -> IO (Either Failed ((C (l1 ⊔ l2) ∧ I(l1 ∨ l2) ∧ I {-A-} (l1 ∧ l2))!a))
sSelect a b = do 
  forceEitherUntil 10000000 a b >>= \case
      Right (Left Fail) -> return $ Left Fail
      Left (Left Fail) -> return $ Left Fail
      Left (Right (Seal a')) -> return $ Right (Seal a')
      Right (Right (Seal b')) -> return $ Right (Seal b')

sSelect' :: forall l1 l2 m m' a pc. (CanFail m, Eq a, pc ⊑ l1, pc ⊑ l2) => (SPrin pc)
  -> Labeled IO pc (m (l1!a)) 
  -> Labeled IO pc (m (l2!a))
  -> Labeled IO pc (pc!(Either Failed ((C (l1 ⊔ l2) ∧ I(l1 ∨ l2) ∧ I {-A-} (l1 ∧ l2))!a)))
sSelect' pc a' b' = do
  a <- a'
  b <- b'  
  restrict pc (\_ ->
    (liftIO $ forceEitherUntil 10000000 a b) >>= \case
        Right (Left Fail) -> return $ Left Fail
        Left (Left Fail) -> return $ Left Fail
        Left (Right (Seal a')) -> return $ Right (Seal a')
        Right (Right (Seal b')) -> return $ Right (Seal b')
        )

sSelect'' :: forall l1 l2 m m' a pc. (CanFail m, Eq a, pc ⊑ l1, pc ⊑ l2) => 
   IO (m (l1!a)) 
  -> IO (m (l2!a))
  -> IO ((Either Failed ((C (l1 ⊔ l2) ∧ I(l1 ∨ l2) ∧ I {-A-} (l1 ∧ l2))!a)))
sSelect'' a' b' = do
  a <- a'
  b <- b'  
  forceEitherUntil 10000000 a b >>= \case
        Right (Left Fail) -> return $ Left Fail
        Left (Left Fail) -> return $ Left Fail
        Left (Right (Seal a')) -> return $ Right (Seal a')
        Right (Right (Seal b')) -> return $ Right (Seal b')


sCompare :: forall l1 l2 m m' a. (CanFail m, Eq a) => m (l1!a) -> m (l2!a)
  -> IO (Either Failed ((C (l1 ⊔ l2) ∧ I(l1 ∧ l2) ∧ I {-A-} (l1 ∨ l2))!a))
sCompare a b = 
  forceEitherUntil 10000000 a b >>= \case
    Left (Left Fail) -> return (Left Fail)
    Left (Right (Seal a')) -> 
      forceUntil 10000000 b >>= \case 
        Left Fail -> return $ Left Fail
        Right (Seal b') -> return $ if a' == b' then Right (Seal a') else Left Fail

    Right (Left Fail) -> return (Left Fail)
    Right (Right (Seal b')) -> 
      forceUntil 10000000 a >>= \case 
        Left Fail -> return $ Left Fail
        Right (Seal a') -> return $ if a' == b' then Right (Seal b') else Left Fail

sCompare' :: forall l1 l2 m m' a pc. (CanFail m, Eq a, pc ⊑ l1, pc ⊑ l2) => (SPrin pc)
  -> Labeled IO pc (m (l1!a)) 
  -> Labeled IO pc (m (l2!a))
  -> Labeled IO pc (pc!(Either Failed ((C (l1 ⊔ l2) ∧ I(l1 ∧ l2) ∧ I {-A-} (l1 ∨ l2))!a)))
sCompare' pc a' b' = do
  a <- a'
  b <- b'
  restrict pc (\_ -> 
      (liftIO $ forceEitherUntil 10000000 a b) >>= \case
        Left (Left Fail) -> return (Left Fail)
        Left (Right (Seal a')) -> 
           (liftIO $ forceUntil 10000000 b) >>= \case 
            Left Fail -> return $ Left Fail
            Right (Seal b') -> return $ if a' == b' then Right (Seal a') else Left Fail

        Right (Left Fail) -> return (Left Fail)
        Right (Right (Seal b')) -> 
           (liftIO $ forceUntil 10000000 a) >>= \case 
            Left Fail -> return $ Left Fail
            Right (Seal a') -> return $ if a' == b' then Right (Seal b') else Left Fail
    )

sCompare'' :: forall l1 l2 m m' a pc. (CanFail m, Eq a, pc ⊑ l1, pc ⊑ l2) => 
     IO (m (l1!a)) 
  -> IO (m (l2!a))
  -> IO ((Either Failed ((C (l1 ⊔ l2) ∧ I(l1 ∧ l2) ∧ I {-A-} (l1 ∨ l2))!a)))
sCompare'' a' b' = do
  a <- a'
  b <- b'
  forceEitherUntil 10000000 a b >>= \case
        Left (Left Fail) -> return (Left Fail)
        Left (Right (Seal a')) -> 
          forceUntil 10000000 b >>= \case 
            Left Fail -> return $ Left Fail
            Right (Seal b') -> return $ if a' == b' then Right (Seal a') else Left Fail

        Right (Left Fail) -> return (Left Fail)
        Right (Right (Seal b')) -> 
          forceUntil 10000000 a >>= \case 
            Left Fail -> return $ Left Fail
            Right (Seal a') -> return $ if a' == b' then Right (Seal b') else Left Fail


majorityQuorum :: Labeled (Choreo IO) ABC ((ABC ! ())  @ "client")
majorityQuorum = do 
 
  (abc, client, abc, fromClient) `sLocally` (\_ -> do
             safePutStrLn @ABC $ label "client waiting for consensus::")

  a <- (abc, locA, abc, fromA) `sLocally` (\_ -> do
             safePutStrLn @ABC $ label "Enter value at A::"
             relabel' abc aGetLine)

  b <- (abc, locB, abc, fromB) `sLocally` (\_ -> do
             safePutStrLn @ABC $ label "Enter value at B::"
             relabel' abc bGetLine)

  c <- (abc, locC, abc, fromC) `sLocally` (\_ -> do
             safePutStrLn @ABC $ label "Enter value at C::"
             relabel' abc cGetLine)

  a' <- (sym locA, abc, fromA, a) ~>: sym client
  b' <- (sym locB, abc, fromB, b) ~>: sym client
  c' <- (sym locC, abc, fromC, c) ~>: sym client

  con <- (abc, client, abc, fromClient) `sLocally` \un -> do  -- almost nested with Labeled IO
      ab <- (sCompare' abc (return (un a')) (return (un b'))) 
      bc <- (sCompare' abc (return (un b')) (return (un c')))
      ca <- (sCompare' abc (return (un c')) (return (un a')))
      abbc <- use ab (\ab' -> (use bc (\bc' -> sSelect' abc (return ab') (return bc'))))
      use abbc (\abbc' -> use ca (\ca'-> sSelect' abc (return abbc') (return ca')))   

  (abc, client, abc, fromClient) `sLocally` \un -> do
    use @_ @ABC @ABC @ABC (un con) (\d' -> do 
      case d' of 
        Right e -> safePutStrLn @ABC $ label "Labeled : Some value"
        Left _ -> safePutStrLn @ABC $ label "Labeled : Failed"
       )

  con' <- (abc, client, abc, fromClient) `sLocally` \un -> do  -- nested with IO 
    restrict abc (\_ -> do 
        sSelect'' (sSelect'' (sCompare'' (return (un a')) (return (un b'))) 
         (sCompare'' (return (un b')) (return (un c')))) (sCompare'' (return (un a')) (return (un c'))))
  
  (abc, client, abc, fromClient) `sLocally` \un -> do
    use @_ @ABC @ABC @ABC (un con') (\d' -> do 
      case d' of 
        Right e -> safePutStrLn @ABC $ label "nested IO : Some value"
        Left _ -> safePutStrLn @ABC $ label "nested IO : Failed"
       )

  ab <- (abc, client, abc, fromClient) `sLocally` \un -> do
       restrict @_ @_ @ABC abc (\_ -> (do 
         sCompare (un a') (un b')))
  
  (abc, client, abc, fromClient) `sLocally` \un -> do
    use @_ @ABC @ABC @ABC (un ab) (\d' -> do 
      case d' of 
        Right e -> safePutStrLn @ABC $ label "ab: Some value"
        Left _ -> safePutStrLn @ABC $ label "ab: Failed"
       )
   
  bc <- (abc, client, abc, fromClient) `sLocally` \un -> do
       restrict @_ @_ @ABC abc (\_ -> (do 
         sCompare (un b') (un c')))

  (abc, client, abc, fromClient) `sLocally` \un -> do
    use @_ @ABC @ABC @ABC (un bc) (\d' -> do 
      case d' of 
        Right e -> safePutStrLn @ABC $ label "bc: Some value"
        Left _ -> safePutStrLn @ABC $ label "bc: Failed"
       )
   
  ca <- (abc, client, abc, fromClient) `sLocally` \un -> do
        restrict @_ @_ @ABC abc (\_ -> (do 
         sCompare (un c') (un a')))

  (abc, client, abc, fromClient) `sLocally` \un -> do
    use @_ @ABC @ABC @ABC (un ca) (\d' -> do 
      case d' of 
        Right e -> safePutStrLn @ABC $ label "ca: Some value"
        Left _ -> safePutStrLn @ABC $ label "ca: Failed"
       )
   
  abc' <- (abc, client, abc, fromClient) `sLocally` \un -> do
    use @_ @ABC @ABC @ABC (un ab) (\ab -> use @_ @ABC @ABC @ABC (un bc) (\bc -> 
      restrict @_ @_ @ABC abc (\_ -> do
              (sSelect (ab) (bc)
                )))) 

  (abc, client, abc, fromClient) `sLocally` \un -> do
    use @_ @ABC @ABC @ABC (un abc') (\d' -> do 
      case d' of 
        Right e -> safePutStrLn @ABC $ label "ab/bc: Some value"
        Left _ -> safePutStrLn @ABC $ label "ab/bc: Failed"
       )
   
  conn <- (abc, client, abc, fromClient) `sLocally` \un -> do
    use @_ @ABC @ABC @ABC (un ca) (\ca -> use @_ @ABC @ABC @ABC (un abc') (\abc' -> 
      restrict @_ @_ @ABC abc (\_ -> do
              (sSelect (abc') (ca)
                )))) 

  (abc, client, abc, fromClient) `sLocally` \un -> do
    use @_ @ABC @ABC @ABC (un conn) (\d' -> do 
      case d' of 
        Right e -> safePutStrLn @ABC $ label "ab/bc/ca: Some value"
        Left _ -> safePutStrLn @ABC $ label "ab/bc/ca: Failed"
       )
   
  a <- (abc, locA, abc, fromA) `sLocally` (\_ -> do
             relabel' abc aGetLine)

  b <- (abc, locB, abc, fromB) `sLocally` (\_ -> do
             relabel' abc bGetLine)

  c <- (abc, locC, abc, fromC) `sLocally` (\_ -> do
             relabel' abc cGetLine)
 
  (abc, client, abc, fromClient) `sLocally` \un -> do
              safePutStrLn @ABC $ label "-"

quorumMain :: HttpConfig -> IO () -- this one needs A B and C to run until Client performs wait()
quorumMain cfg = do
  [loc] <- getArgs
  case loc of
    "client" -> runChoreography cfg (runLabeled  majorityQuorum) "client"
    "A" -> runChoreography cfg (runLabeled  majorityQuorum) "A"
    "B" -> runChoreography cfg (runLabeled  majorityQuorum) "B"
    "C" -> runChoreography cfg (runLabeled  majorityQuorum) "C"
  return ()


-- quorumMain :: HttpConfig -> Int -> IO ()
-- quorumMain cfg cnt = do
--   putStrLn $ "--------------------" ++ (show cnt)
--   [loc] <- getArgs
--   runChoreography cfg (runLabeled  majorityQuorum) loc >> return () >> quorumMain cfg (cnt+1)
 
main = do 
  quorumMain cfg
  -- quorumMain cfg 0
 where
    cfg = mkHttpConfig [ ("A", ("localhost", 4242))
                       , ("B", ("localhost", 4343))
                       , ("C", ("localhost", 4544))
                       , ("client", ("localhost", 4546))
                       ]

--main = majorityQuorumMain