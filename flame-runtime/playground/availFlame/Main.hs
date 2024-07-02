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
--import Prelude hiding (compare)
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


type Client = N "client"
client :: SPrin Client
client = SName (Proxy :: Proxy "client")

type B1 = N "b1"
b1 :: SPrin B1
b1 = SName (Proxy :: Proxy "b1")

type B2 = N "b2"
b2 :: SPrin B2
b2 = SName (Proxy :: Proxy "b2")

-- type BS = (Client \/ B1)

type BS = ((Client \/ B1) \/ B2)

-- bs :: SPrin BS
-- bs = client *\/ b1

bs :: SPrin BS
bs = ((client *\/ b1) *\/ b2)


-- type FromClient = BS
-- fromClient :: SPrin BS
-- fromClient = bs

-- type FromB1 = BS
-- fromB1 :: SPrin BS
-- fromB1 = bs

type FromClient = BS
fromClient :: SPrin BS
fromClient = bs

type FromB1 = BS
fromB1 :: SPrin BS
fromB1 = bs

type FromB2 = BS
fromB2 :: SPrin BS
fromB2 = bs



instance Show a => Show (l ! a) where
  show (Seal x) = "Seal " ++ show x
instance Read a => Read (l ! a) where
  readsPrec _ s = [(Seal x, rest) | ("Seal", rest1) <- lex s, (x, rest) <- readsPrec 0 rest1]
instance Eq a => Eq (l ! a) where
  (Seal a) == (Seal b) = a == b
instance Ord a => Ord (l ! a) where
  compare (Seal x) (Seal y) = compare x y

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

-- | Conditionally execute choreographies based on a located value.
sCond ::  forall pc l loc m a b. (Show a, Read a, KnownSymbol loc, pc ⊑ l)
     => (Proxy loc, SPrin pc, a @ loc) -- ^ A pair of a location and a scrutinee located on
                                         -- it.
     -> (a -> Labeled (Choreo m) pc b) -- ^ A function that describes the follow-up
                          -- choreographies based on the value of scrutinee.
     -> Labeled (Choreo m) pc (l!b)
sCond (l, pc, la) c = restrict pc $ \_ -> cond' (l, la) (\un -> runLabeled $ c un)

sPutStrLn :: Show a => SPrin pc -> (l ⊑ pc) => l!a -> Labeled IO pc (pc!())
sPutStrLn pc la = restrict pc (\open -> print (open la))

sGetLine :: SPrin pc -> Labeled IO pc (pc!Int)
sGetLine pc = restrict pc (\_ -> readLn)

safePutStrLn :: forall l a. (Show a, l ⊑ BS) => l!a
                      -> Labeled IO BS (BS!())
safePutStrLn =  sPutStrLn bs

clientGetLine :: Labeled IO FromClient (FromClient!Int)
clientGetLine = sGetLine fromClient

b1GetLine :: Labeled IO FromB1 (FromB1!Int)
b1GetLine = sGetLine fromB1

b2GetLine :: Labeled IO FromB2 (FromB2!Int)
b2GetLine = sGetLine fromB2
-- instance HasFail (BS!a) where
--   failVal = ()
timeOut :: Int 
timeOut = 10000000

data Failed = Fail
instance Show Failed where
    show Fail = "Fail"

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

sSelect' :: forall l1 l2 m m' a pc. (CanFail m, Eq a, pc ⊑ l1, pc ⊑ l2) => (SPrin pc)
  -> Labeled IO pc (m (l1!a)) 
  -> Labeled IO pc (m (l2!a))
  -> Labeled IO pc (pc!(Either Failed ((C (l1 ⊔ l2) ∧ I(l1 ∨ l2) ∧ A(l1 ∧ l2))!a)))
sSelect' pc a' b' = do
  a <- a'
  b <- b'  
  restrict pc (\_ ->
    (liftIO $ forceEitherUntil timeOut a b) >>= \case
        Right (Left Fail) -> return $ Left Fail
        Left (Left Fail) -> return $ Left Fail
        Left (Right (Seal a')) -> return $ Right (Seal a')
        Right (Right (Seal b')) -> return $ Right (Seal b')
        )

largest ::forall l1 l2 m a pc. (CanFail m, Eq a, pc ⊑ l1, pc ⊑ l2, Show a, Ord a) => (SPrin pc)
  ->   Labeled IO pc (m (l1!a)) 
  -> Labeled IO pc (m (l2!a))
  -> Labeled IO pc (pc!(Either Failed ((C (l1 ⊔ l2) ∧ I(l1 ∧ l2) ∧ A(l1 ∨ l2))!a)))
largest pc a' b' = do
  a <- a'
  b <- b'
  restrict pc (\_ -> 
      (liftIO $ forceEitherUntil timeOut a b) >>= \case
        Left (Left Fail) -> return (Left Fail)
        Left (Right (Seal a')) -> 
           (liftIO $ forceUntil timeOut b) >>= \case 
            Left Fail -> return $ Left Fail
            Right (Seal b') -> return $ if a' > b' then Right (Seal a') else Right (Seal b')

        Right (Left Fail) -> return (Left Fail)
        Right (Right (Seal b')) -> 
           (liftIO $ forceUntil timeOut a) >>= \case 
            Left Fail -> return $ Left Fail
            Right (Seal a') -> return $ if a' > b' then Right (Seal b') else Right (Seal b')
    )


largestAvailableBalance :: Labeled (Choreo IO) BS ((BS ! (Int)) @ "client")
largestAvailableBalance = do
  (bs, client, bs, fromClient) `sLocally` (\_ -> do
             safePutStrLn @BS $ label "Client waiting to get the largest balance:")
           
  bal1 <- (bs, b1, bs, fromB1) `sLocally` (\_ -> do
             safePutStrLn @BS $ label "Enter balance at b1:"
             relabel' bs b1GetLine)

  bal2 <- (bs, b2, bs, fromB2) `sLocally` (\_ -> do
             safePutStrLn @BS $ label "Enter balance at b2:"
             relabel' bs b2GetLine)

  bal1' <- (sym b1, bs, fromB1, bal1) ~>: sym client
  bal2' <- (sym b2, bs, fromB2, bal2) ~>: sym client

  -- largest <- (bs, client, bs, fromClient) `sLocally` \un -> do
  --         restrict @_ @_ @BS bs (\_ -> (do 
  --           largest @BS @BS @BS (un bal1') (un bal2') ))
          
  available <- (bs, client, bs, fromClient) `sLocally` \un -> do  -- almost nested with Labeled IO
      bal <- (largest bs (return (un bal1')) (return (un bal2')))
      sel <- (sSelect' bs (return (un bal1')) (return (un bal2'))) 
      use bal (\bal' -> use sel (\sel'-> sSelect' bs (return bal') (return sel')))   

  -- available <- (bs, client, bs, fromClient) `sLocally` \un -> do
  --   (sSelect' bs (return (un bal1')) (return (un bal2'))) 
   
  (bs, b2, bs, fromB2) `sLocally` (\un -> do
             relabel' bs b2GetLine)
  
  (bs, b1, bs, fromB1) `sLocally` (\un -> do
             relabel' bs b1GetLine)

  (bs, client, bs, fromClient) `sLocally` \un -> do
              safePutStrLn @BS $ label "largest available balance:"
              safePutStrLn @BS $ (un available)
              relabel' bs clientGetLine
 
main :: IO ()
main = do
  [loc] <- getArgs
  case loc of
    "client"  -> runChoreography cfg (runLabeled largestAvailableBalance) "client"
    "b1" -> runChoreography cfg (runLabeled largestAvailableBalance) "b1"
    "b2" -> runChoreography cfg (runLabeled largestAvailableBalance) "b2"
  return ()
  where
    cfg = mkHttpConfig [ ("client",  ("localhost", 4242))
                       , ("b1", ("localhost", 4343))
                       , ("b2", ("localhost", 4344))
                       ]



-- sSelect :: forall l l' l'' a. (HasFail a, Eq a, l ⊑ l'', l' ⊑ l'', Show a) => 
--     Async (l!(l'!a)) -> Async (l!(l'!a)) -> IO (Async (l!(l'!a)))
-- sSelect a b = do
--     a' <- timeout time (wait a)
--     case a' of 
--       (Just e) -> do 
--         let e1 = join e
--         case e1 of 
--           Seal c | c /= failVal -> do 
--             return a --async (return e1)
--           _ -> do 
--                 b' <- timeout time (wait b)
--                 case b' of 
--                   (Just e) -> do
--                     let b1 = join e
--                     return b -- async (return b1) 
--                   Nothing -> async (return (Seal (Seal failVal)))
--       _ -> do -- Nothing i.e. a did not arrive
--          b' <- timeout time (wait b)
--          case b' of 
--           (Just e) -> do 
--             let b1' = join e
--             return b -- async( return b1')
--           Nothing -> do 
--             async (return (Seal (Seal failVal)))                       