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

module Main where

-- import Choreography
-- import Choreography.Choreo
-- import Choreography.Location

import Control.Concurrent.Async
import Control.Concurrent.STM

import MyHasChor.Choreography.ChoreoAsync
import MyHasChor.Choreography.Location
import MyHasChor.Choreography.NetworkAsync ()
import MyHasChor.Choreography.NetworkAsync.Http

import Data.Proxy
import Data.Time
import Data.Maybe (isJust, fromJust)
import System.Environment
import GHC.TypeLits

import Flame.Principals
import Flame.TCB.Freer.IFC
import Data.Either (isLeft)
import System.Timeout (timeout)

maybeToEither :: e -> Maybe a -> Either e a
maybeToEither e Nothing = Left e
maybeToEither _ (Just a) = Right a

type Buyer = N "buyer"
buyer :: SPrin Buyer
buyer = SName (Proxy :: Proxy "buyer")

type Buyer2 = N "buyer2"
buyer2 :: SPrin Buyer2
buyer2 = SName (Proxy :: Proxy "buyer2")


type Seller = N "seller"
seller :: SPrin Seller
seller = SName (Proxy :: Proxy "seller")

type BS = (Buyer \/ Seller \/ Buyer2)

bs :: SPrin BS
bs = buyer *\/ seller *\/ buyer2

type FromBuyer = BS
fromBuyer :: SPrin BS
fromBuyer = bs

type FromBuyer2 = BS
fromBuyer2 :: SPrin BS
fromBuyer2 = bs

type FromSeller = BS
fromSeller :: SPrin BS
fromSeller = bs

-- type FromBuyer = ((C (Buyer \/ Seller)) /\ (I Buyer))
-- fromBuyer :: SPrin FromBuyer
-- fromBuyer = (((buyer *\/ seller)*->) */\ (buyer*<-))

-- type FromSeller = ((C (Buyer \/ Seller)) /\ (I Seller))
-- fromSeller :: SPrin FromSeller
-- fromSeller = (((buyer *\/ seller)*->) */\ (seller*<-))

-- cond :: (Show a, Read a, KnownSymbol l)
--      => (Proxy l, a @ l)  -- ^ A pair of a location and a scrutinee located on
--                           -- it.
--      -> (a -> Choreo m b) -- ^ A function that describes the follow-up
--                           -- choreographies based on the value of scrutinee.
--      -> Choreo m b
-- cond (l, a) c = undefined -- stub for type signature

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

--TODO: Async it up
-- | Perform a local computation at a given location.
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
-- sCond ::  forall pc l loc m a b. (Show a, Read a, KnownSymbol loc, pc ⊑ l)
--      => (Proxy loc, SPrin pc, a @ loc) -- ^ A pair of a location and a scrutinee located on
--                                          -- it.
--      -> (a -> Labeled (Choreo m) pc b) -- ^ A function that describes the follow-up
--                           -- choreographies based on the value of scrutinee.
--      -> Labeled (Choreo m) pc (l!b)
-- sCond (l, pc, la) c = restrict pc $ \_ -> cond (l, la) (\un -> runLabeled $ c un)

sPutStrLn :: Show a => SPrin pc -> (l ⊑ pc) => l!a -> Labeled IO pc (pc!())
sPutStrLn pc la = restrict pc (\open -> print (open la))

sGetLine :: SPrin pc -> Labeled IO pc (pc!String)
sGetLine pc = restrict pc (\_ -> getLine)

safePutStrLn :: forall l a. (Show a, l ⊑ BS) => l!a
                      -> Labeled IO BS (BS!())
safePutStrLn =  sPutStrLn bs

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
  forceEither a b = return $ Left a


sSelect :: forall l1 l2 m m' a. (CanFail m, Eq a) => m (l1!a) -> m (l2!a)
  -> IO (Either Failed ((C (l1 ⊔ l2) ∧ I(l1 ∨ l2) ∧ I {-A-} (l1 ∧ l2))!a))
sSelect a b = do 
    c <- forceEitherUntil 10000000 a b
    case c of 
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

buyerGetLine :: Labeled IO FromBuyer (FromBuyer!String)
buyerGetLine = sGetLine fromBuyer

buyerGetLine2 :: Labeled IO FromBuyer2 (FromBuyer2!String)
buyerGetLine2 = sGetLine fromBuyer2

-- | `bookseller` is a choreography that implements the bookseller protocol.

instance Show a => Show (l ! a) where
  show (Seal x) = "Seal " ++ show x
instance Read a => Read (l ! a) where
  readsPrec _ s = [(Seal x, rest) | ("Seal", rest1) <- lex s, (x, rest) <- readsPrec 0 rest1]

instance Eq a => Eq (l ! a) where
  (Seal a) == (Seal b) = a == b


majorityQuorum :: Labeled (Choreo IO) BS ((BS ! ())  @ "seller")
majorityQuorum = do  
  a <- (bs, buyer, bs, fromBuyer) `sLocally` (\_ -> do
             safePutStrLn @BS $ label "Enter value at buyer::"
             relabel' bs buyerGetLine)

  b <- (bs, buyer2, bs, fromBuyer2) `sLocally` (\_ -> do
             safePutStrLn @BS $ label "Enter value at buyer2::"
             relabel' bs buyerGetLine2)

  a' <- (sym buyer, bs, fromBuyer, a) ~>: sym seller
  b' <- (sym buyer2, bs, fromBuyer2, b) ~>: sym seller
  
  c <- (bs, seller, bs, fromSeller) `sLocally` \un -> do restrict bs (\_ -> do sCompare (un b') (un a'))
  d <- (bs, seller, bs, fromSeller) `sLocally` \un -> do restrict bs (\_ -> do sSelect (un a') (un b'))

  (bs, seller, bs, fromSeller) `sLocally` \un -> do
    use @_ @BS @BS @BS (un c) (\c' -> do 
      case c' of 
        Right e -> safePutStrLn @BS $ label "Compare: Some value"
        Left _ -> safePutStrLn @BS $ label "Compare: Failed"
       )
  (bs, seller, bs, fromSeller) `sLocally` \un -> do
    use @_ @BS @BS @BS (un d) (\d' -> do 
      case d' of 
        Right e -> safePutStrLn @BS $ label "Select: Some value"
        Left _ -> safePutStrLn @BS $ label "Select: Failed"
       )
  
  (bs, buyer, bs, fromBuyer) `sLocally` \_-> relabel' bs buyerGetLine
  (bs, buyer2, bs, fromBuyer2) `sLocally` \_-> relabel' bs buyerGetLine2
  (bs, seller, bs, fromSeller) `sLocally` \_-> safePutStrLn @BS $ label "compare/select done at seller"

  -- try nested select compare -- working with IO r.n. what about Labeled monad ?
  -- support for Reads/Eq for Sealed values 
  -- support for availability 
  -- moving restrict inside of select/compare functions



quorumMain :: HttpConfig -> IO ()
quorumMain cfg = do
  [loc] <- getArgs
  runChoreography cfg (runLabeled  majorityQuorum) loc
  return () 
 
main = do 
  quorumMain cfg 
 where
    cfg = mkHttpConfig [ ("buyer", ("localhost", 4242))
                       , ("buyer", ("localhost", 4242))
                       , ("seller", ("localhost", 4343))
                       ]