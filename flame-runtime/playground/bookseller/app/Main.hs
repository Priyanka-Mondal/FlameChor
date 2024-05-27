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

import Control.Concurrent.Async (poll, wait, waitEitherCatch, waitCatch, Async)
import Control.Concurrent.STM

import Choreography.ChoreoAsync
import Choreography.Location
import Choreography.NetworkAsync ()
import Choreography.NetworkAsync.Http

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

type Seller = N "seller"
seller :: SPrin Seller
seller = SName (Proxy :: Proxy "seller")

type BS = (Buyer \/ Seller)

bs :: SPrin BS
bs = buyer *\/ seller

type FromBuyer = BS
fromBuyer :: SPrin BS
fromBuyer = bs

type FromSeller = BS
fromSeller :: SPrin BS
fromSeller = bs

-- type FromBuyer = ((C (Buyer \/ Seller)) /\ (I Buyer))
-- fromBuyer :: SPrin FromBuyer
-- fromBuyer = (((buyer *\/ seller)*->) */\ (buyer*<-))

-- type FromSeller = ((C (Buyer \/ Seller)) /\ (I Seller))
-- fromSeller :: SPrin FromSeller
-- fromSeller = (((buyer *\/ seller)*->) */\ (seller*<-))

cond :: (Show a, Read a, KnownSymbol l)
     => (Proxy l, a @ l)  -- ^ A pair of a location and a scrutinee located on
                          -- it.
     -> (a -> Choreo m b) -- ^ A function that describes the follow-up
                          -- choreographies based on the value of scrutinee.
     -> Choreo m b
cond (l, a) c = undefined -- stub for type signature

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
sCond ::  forall pc l loc m a b. (Show a, Read a, KnownSymbol loc, pc ⊑ l)
     => (Proxy loc, SPrin pc, a @ loc) -- ^ A pair of a location and a scrutinee located on
                                         -- it.
     -> (a -> Labeled (Choreo m) pc b) -- ^ A function that describes the follow-up
                          -- choreographies based on the value of scrutinee.
     -> Labeled (Choreo m) pc (l!b)
sCond (l, pc, la) c = restrict pc $ \_ -> cond (l, la) (\un -> runLabeled $ c un)

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
                    -- if there was a concurrently' that behaved more like waitEitherCatch 
                    -- then maybe I could mix CanFail instances here by using `force` 
                    -- instead of `wait`. Currently the non-Async instance would need to 
                    -- be inside an async

instance (CanFail (Either Failed)) where
  force = return
  forceEither a b = return $ Left a

sCompare :: forall l1 l2 m a. (CanFail m, Eq a) => Int -> m (l1!a) -> m (l2!a)
  -> IO (Either Failed ((C (l1 ⊔ l2) ∧ I(l1 ∧ l2) ∧ I {-A-} (l1 ∨ l2))!a))
sCompare t a b = 
  forceEitherUntil t a b >>= \case
    Left (Left Fail) -> return (Left Fail)
    Left (Right (Seal a')) -> 
      forceUntil t b >>= \case
        Left Fail -> return $ Left Fail
        Right (Seal b') -> return $ if a' == b' then Right (Seal a') else Left Fail

    Right (Left Fail) -> return (Left Fail)
    Right (Right (Seal b')) -> 
      forceUntil t a >>= \case
        Left Fail -> return $ Left Fail
        Right (Seal a') -> return $ if a' == b' then Right (Seal b') else Left Fail

buyerGetLine :: Labeled IO FromBuyer (FromBuyer!String)
buyerGetLine = sGetLine fromBuyer

-- | `bookseller` is a choreography that implements the bookseller protocol.
bookseller :: Labeled (Choreo IO) BS ((BS ! (FromBuyer ! Maybe Day)) @ "buyer")
bookseller = do
  -- the buyer node prompts the user to enter the title of the book to buy
  title <- (bs, buyer, bs, fromBuyer) `sLocally` (\_ -> do
             safePutStrLn $ label "Enter the title of the book to buy"
             relabel' bs buyerGetLine)

  -- the buyer sends the title to the seller
  title' <- (sym buyer, bs, fromBuyer, title) ~>: sym seller

  -- the seller checks the price of the book
  price <- (bs, seller, bs, fromSeller) `sLocally` \un -> do
              title'' <- join . join @_ @_ @BS <$> restrict @_ @_ @BS bs (\_ -> wait (un title'))
              use title'' (protect @_ @BS. priceOf)

  -- the seller sends back the price of the book to the buyer
  price' <- (sym seller, bs, fromSeller, price) ~>: sym buyer

  -- the buyer decides whether to buy the book or not
  decision <- (bs, buyer, bs, fromBuyer) `sLocally` \un -> do
                 (price'' :: BS!Int) <- join . join @_ @_ @BS <$> restrict @_ @_ @BS bs (\_ -> wait (un price'))
                 use @_ @_ @_ @BS price'' (\p -> protect (p < budget))

  -- if the buyer decides to buy the book, the seller sends the delivery date to the buyer
  labelInM (sCond (sym buyer, bs, decision) (\d -> do -- labelInM $ use d 
    -- (d' ::  BS ! (BS ! Bool)) <- restrict bs {- fromBuyer -} (\_ -> wait d)
    labelInM $ use @_ @_ @_ @BS d (\case
      True -> do
        deliveryDate  <- (bs, seller, bs, fromSeller) `sLocally` (\un -> do
          (title'' :: BS!String) <- join . join @_ @_ @BS <$> restrict @_ @_ @BS bs {- fromSeller -} (\_ -> wait (un title'))
          use title'' (\t -> protect @_ @BS $ deliveryDateOf t))
        deliveryDate' <- ((sym seller, bs, fromSeller, deliveryDate) ~>: sym buyer)

        labelOutM ((bs, buyer, bs, fromBuyer) `sLocally` (\un -> do
          (deliveryDate'' :: BS!Day) <- join . join @_ @_ @BS  <$> restrict @_ @_ @BS bs {- fromBuyer -} (\_ -> wait (un deliveryDate'))
          use @_ @_ @_ @BS deliveryDate''
            (\dd -> do
              safePutStrLn $ label ("The book will be delivered on " ++ show dd)
              protect @_ @BS $ Just dd)))

      False -> labelOutM ((bs, buyer, bs, fromBuyer) `sLocally` (\un -> do
          safePutStrLn $ label "The book's price is out of the budget"
          protect Nothing)))))

budget :: Int
budget = 100

priceOf :: String -> Int
priceOf "Types and Programming Languages" = 80
priceOf "Homotopy Type Theory"            = 120

deliveryDateOf :: String -> Day
deliveryDateOf "Types and Programming Languages" = fromGregorian 2022 12 19
deliveryDateOf "Homotopy Type Theory"            = fromGregorian 2023 01 01

main :: IO ()
main = do
  [loc] <- getArgs
  case loc of
    "buyer"  -> runChoreography cfg (runLabeled bookseller) "buyer"
    "seller" -> runChoreography cfg (runLabeled bookseller) "seller"
  return ()
  where
    cfg = mkHttpConfig [ ("buyer",  ("localhost", 4242))
                       , ("seller", ("localhost", 4343))
                       ]