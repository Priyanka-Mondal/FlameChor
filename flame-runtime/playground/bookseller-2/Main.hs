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
import Control.Concurrent.Async
import MyHasChor.Choreography.ChoreoAsync
import MyHasChor.Choreography.Location
import MyHasChor.Choreography.NetworkAsync
import MyHasChor.Choreography.NetworkAsync.Http
import Data.Proxy
import Data.Time
import System.Environment
import GHC.TypeLits

import Flame.Principals
import Flame.TCB.Freer.IFC

type Buyer = N "buyer"
buyer :: SPrin Buyer
buyer = SName (Proxy :: Proxy "buyer")

type Seller = N "seller"
seller :: SPrin Seller
seller = SName (Proxy :: Proxy "seller")

type Seller2 = N "seller2"
seller2 :: SPrin Seller2
seller2 = SName (Proxy :: Proxy "seller2")

-- type BS = (Buyer \/ Seller)

type BS = ((Buyer \/ Seller) \/ Seller2)

-- bs :: SPrin BS
-- bs = buyer *\/ seller

bs :: SPrin BS
bs = ((buyer *\/ seller) *\/ seller2)


-- type FromBuyer = BS
-- fromBuyer :: SPrin BS
-- fromBuyer = bs

-- type FromSeller = BS
-- fromSeller :: SPrin BS
-- fromSeller = bs

type FromBuyer = BS
fromBuyer :: SPrin BS
fromBuyer = bs

type FromSeller = BS
fromSeller :: SPrin BS
fromSeller = bs

type FromSeller2 = BS
fromSeller2 :: SPrin BS
fromSeller2 = bs



instance Show a => Show (l ! a) where
  show (Seal x) = "Seal " ++ show x
instance Read a => Read (l ! a) where
  readsPrec _ s = [(Seal x, rest) | ("Seal", rest1) <- lex s, (x, rest) <- readsPrec 0 rest1]


-- type FromBuyer = ((C (Buyer \/ Seller)) /\ (I Buyer))
-- fromBuyer :: SPrin FromBuyer
-- fromBuyer = (((buyer *\/ seller)*->) */\ (buyer*<-))

-- type FromSeller = ((C (Buyer \/ Seller)) /\ (I Seller))
-- fromSeller :: SPrin FromSeller
-- fromSeller = (((buyer *\/ seller)*->) */\ (seller*<-))

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
sCond (l, pc, la) c = restrict pc $ \_ -> cond' (l, la) (\un -> runLabeled $ c un)

sPutStrLn :: Show a => SPrin pc -> (l ⊑ pc) => l!a -> Labeled IO pc (pc!())
sPutStrLn pc la = restrict pc (\open -> print (open la))

sGetLine :: SPrin pc -> Labeled IO pc (pc!String)
sGetLine pc = restrict pc (\_ -> getLine)

safePutStrLn :: forall l a. (Show a, l ⊑ BS) => l!a
                      -> Labeled IO BS (BS!())
safePutStrLn =  sPutStrLn bs

buyerGetLine :: Labeled IO FromBuyer (FromBuyer!String)
buyerGetLine = sGetLine fromBuyer

sellerGetLine :: Labeled IO FromSeller (FromSeller!String)
sellerGetLine = sGetLine fromSeller

-- | `bookseller` is a choreography that implements the bookseller protocol.
bookseller :: Labeled (Choreo IO) BS ((BS ! (String)) @ "seller")
bookseller = do
  -- the buyer node prompts the user to enter the title of the book to buy
  title <- (bs, buyer, bs, fromBuyer) `sLocally` (\_ -> do
             safePutStrLn @BS $ label "Enter the title of the book to buy"
             relabel' bs buyerGetLine)

  -- the buyer sends the title to the seller
  title' <- (sym buyer, bs, fromBuyer, title) ~>: sym seller
  title2' <- (sym buyer, bs, fromBuyer, title) ~>: sym seller2

    -- the seller checks the price of the book
  price <- (bs, seller, bs, fromSeller) `sLocally` \un -> do
              title'' <- join . join @_ @_ @BS <$> restrict @_ @_ @BS bs (\_ -> wait (un title'))
              use title'' (protect @_ @BS. priceOf)
  
  price2 <- (bs, seller2, bs, fromSeller2) `sLocally` \un -> do
              title'' <- join . join @_ @_ @BS <$> restrict @_ @_ @BS bs (\_ -> wait (un title2'))
              use title'' (protect @_ @BS. priceOf2)

  
  -- the seller sends back the price of the book to the buyer
  price' <- (sym seller, bs, fromSeller, price) ~>: sym buyer
  price2' <- (sym seller2, bs, fromSeller2, price2) ~>: sym buyer

  (bs, seller, bs, fromSeller) `sLocally` \un -> do
                 (t1 :: BS!String) <- join . join @_ @_ @BS <$> restrict @_ @_ @BS bs (\_ -> wait (un title'))
                -- (t2 :: BS!String) <- join . join @_ @_ @BS <$> restrict @_ @_ @BS bs (\_ -> wait (un title'))
                 safePutStrLn @BS $ t1
                 --use t'' (protect @_ @BS. priceOf)

  (bs, seller2, bs, fromSeller2) `sLocally` \un -> do
                 (t1 :: BS!String) <- join . join @_ @_ @BS <$> restrict @_ @_ @BS bs (\_ -> wait (un title2'))
                -- (t2 :: BS!String) <- join . join @_ @_ @BS <$> restrict @_ @_ @BS bs (\_ -> wait (un title'))
                 safePutStrLn @BS $ t1

  -- the buyer decides whether to buy the book or not
  large <- (bs, buyer, bs, fromBuyer) `sLocally` \un -> do
             (price1 :: BS! Int) <- join . join @_ @_ @BS <$>  restrict @_ @_ @BS bs (\_ -> (wait (un price')))
             (price2 :: BS! Int) <- join . join @_ @_ @BS <$>  restrict @_ @_ @BS bs (\_ -> (wait (un price2')))
             use @_ @_ @_ @BS price1 (\p -> use @_ @_ @_ @BS price2 (\p2 -> protect (largest (p,p2))))
            
  (bs, buyer, bs, fromBuyer) `sLocally` \un -> do
                 safePutStrLn @BS $ un large
  
  (bs, seller2, bs, fromSeller2) `sLocally` (\un -> do
             safePutStrLn @BS $ un price2
             relabel' bs sellerGetLine)
  
  (bs, seller, bs, fromSeller) `sLocally` (\un -> do
             safePutStrLn @BS $ un price
             relabel' bs sellerGetLine)
  
  -- if the buyer decides to buy the book, the seller sends the delivery date to the buyer
  
budget :: Int
budget = 100

priceOf :: String -> Int
priceOf "T" = 80
priceOf "H"            = 120

priceOf2 :: String -> Int
priceOf2 "T" = 90
priceOf2 "H"            = 100

largest :: (Int , Int) -> Int
largest (a ,b) = if (a > b) then a else b

deliveryDateOf :: String -> Day
deliveryDateOf "T" = fromGregorian 2022 12 19
deliveryDateOf "H"            = fromGregorian 2023 01 01

main :: IO ()
main = do
  [loc] <- getArgs
  case loc of
    "buyer"  -> runChoreography cfg (runLabeled bookseller) "buyer"
    "seller" -> runChoreography cfg (runLabeled bookseller) "seller"
    "seller2" -> runChoreography cfg (runLabeled bookseller) "seller2"
  return ()
  where
    cfg = mkHttpConfig [ ("buyer",  ("localhost", 4242))
                       , ("seller", ("localhost", 4343))
                       , ("seller2", ("localhost", 4344))
                       ]