{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
--{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}


module Main where


import MyHasChor.Choreography
import MyHasChor.Choreography.Choreo
import Control.Concurrent.Async
import Control.Monad.Identity (Identity(..), runIdentity, void)
import MyHasChor.Choreography.Location
import Data.Proxy
import Data.Time
import System.Environment
--import Control.Monad.Identity (Identity(..), runIdentity)
import "freer-simple" Control.Monad.Freer as S
--import "HasChor" Control.Monad.Freer (interpFreer, toFreer)
import MyHasChor.Control.Monad.Freer
import MyHasChor.Choreography.Labelled
import Flame.Principals
import Flame.TCB.Freer.IFC
    ( type (!),
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
import MyHasChor.Choreography.Network.Local --(LocalConfig(locToBuf))

type Buyer = N "buyer"
buyer :: SPrin Buyer
buyer = SName (Proxy :: Proxy "buyer")

type Seller = N "seller"
seller :: SPrin Seller
seller = SName (Proxy :: Proxy "seller")

type BS = (Buyer \/ Seller) 
   --deriving (Show)

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

-- joinIn' :: forall l l' l'' pc m a loc. 
--   (Monad m, l ⊑ l'', l' ⊑ l'', Show a, Read a) => 
--   Labeled m pc (l ! ((l'!a) @ loc)) -> Labeled m pc ((l''!a) @ loc)
-- joinIn' lx = wrap <$> do 
--   x <- lx 
--   let x' = joinIn @l @l' @l'' x -- why didn't this get inferred?
--   use (unwrap x') protect

(~>:) :: forall a loc loc' pc l m. (Show a, Read a, KnownSymbol loc, KnownSymbol loc', Show (l!a), Read (l!a)) --, (N loc') ≽ (C pc), (N loc) ≽ (I pc))
     => (Proxy loc, SPrin pc, SPrin l, (l!a) @ loc)  
                                -- a sender's location, 
                                -- a clearance, 
                                -- and a value located at the sender
     -> Proxy loc'-- ^ A receiver's location.
     -> Labeled (Choreo m) pc ((pc!(l!a)) @ loc')
(~>:) (loc, pc, l, la) loc' = do
  result <- restrict pc ( \_ -> (loc, la) ~> loc')
  return $ labelIn result

-- | Conditionally execute choreographies based on a located value.
sCond ::  forall pc l loc m a b. (Show a, Read a, KnownSymbol loc, pc ⊑ l)
     => (Proxy loc, SPrin pc, a @ loc) -- ^ A pair of a location and a scrutinee located on
                                         -- it.
     -> (a -> Labeled (Choreo m) pc b) -- ^ A function that describes the follow-up
                          -- choreographies based on the value of scrutinee.
     -> Labeled (Choreo m) pc (l ! b)
sCond (l, pc, la) c = restrict pc $ \_ -> cond (l, la) (runLabeled . c)--(\la -> runLabeled $ c la)

------
safePutStrLn :: forall l a. (Show a, l ⊑ BS) => l!a 
                      -> Labeled IO BS (BS!())
safePutStrLn =  sPutStrLn  bs

buyerGetLine :: Labeled IO FromBuyer (FromBuyer!String)
buyerGetLine = sGetLine  fromBuyer

-- | `bookseller` is a choreography that implements the bookseller protocol.
--Choreo IO (Maybe Day @ "buyer")
bookseller :: Labeled (Choreo IO) BS ((BS ! (FromBuyer ! Maybe Day)) @ "buyer")
bookseller = do
  -- the buyer node prompts the user to enter the title of the book to buy
  title <- (bs, buyer, bs, fromBuyer) `slocally` (\_ -> do
             safePutStrLn @BS $ label "Enter the title of the book to buy"
             relabel' bs buyerGetLine)

  -- the buyer sends the title to the seller
  title' <- (sym buyer, bs, fromBuyer, title) ~>: sym seller
  --return title'
 
  -- the seller checks the price of the book
  price <- (bs, seller, bs, fromSeller) `slocally` (\un -> do
    use @_ @_ @_ @BS (join @_ @_ @BS (un title')) (protect . priceOf))
  --  price <- seller `locally` \un -> return $ priceOf (un title')
  
  -- the seller sends back the price of the book to the buyer
  price' <- (sym seller, bs, fromSeller, price) ~>: sym buyer
 
  -- the buyer decides whether to buy the book or not
  decision <- (bs, buyer, bs, fromBuyer) `slocally` (\un -> do
    use @_ @_ @_ @BS (join @_ @_ @BS (un price')) (\p -> protect (p < budget)))
 
  -- if the buyer decides to buy the book, the seller sends the delivery date to the buyer
  labelIn' (sCond (sym buyer, bs, decision) (\d -> labelIn' $ use d (\case
    True  -> do
      deliveryDate  <- (bs, seller, bs, fromSeller) `slocally` (\un -> do
        use @_ @_ @_ @BS (join (un title')) (protect . deliveryDateOf))
      deliveryDate' <- (sym seller, bs, fromSeller, deliveryDate) ~>: sym buyer
 
      labelOut'((bs, buyer, bs, fromBuyer) `slocally` (\un -> do --labelOut'
        use (join (un deliveryDate')) 
          (\dd -> do
            safePutStrLn $ label ("The book will be delivered on " ++ show dd)
            protect $ Just dd)))
 
    False -> labelOut'((bs, buyer, bs, fromBuyer) `slocally` (\un -> do --labelOut'
        safePutStrLn $ label "The book's price is out of the budget"
        protect Nothing))
        )))


budget :: Int
budget = 100

priceOf :: String -> Int
priceOf "Types and Programming Languages" = 80
priceOf "H"            = 20

deliveryDateOf :: String -> Day
deliveryDateOf "Types and Programming Languages" = fromGregorian 2022 12 19
deliveryDateOf "H"            = fromGregorian 2023 01 01

main :: IO ()
main = do
  [loc] <- getArgs
  --Labeled (Choreo IO) BS ((BS ! (FromBuyer ! Maybe Day)) @ "buyer")
  case loc of
    "buyer"  -> runChoreography cfg (runLabeled bookseller) "buyer"
    "seller" -> runChoreography cfg (runLabeled bookseller) "seller"
  --Labeled (Choreo IO) BS ((BS ! (FromBuyer ! Maybe Day)) @ "buyer")
  --Labeled (Choreo IO) ABC ((ABC ! Int)  @ "client")
  return ()
  where
    cfg = mkHttpConfig [ ("buyer",  ("localhost", 4242))
                       , ("seller", ("localhost", 4343))
                       ]

--main :: IO ()
---main = undefined