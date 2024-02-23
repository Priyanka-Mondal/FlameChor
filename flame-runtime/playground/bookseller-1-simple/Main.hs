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
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Main where

import Choreography
import Choreography.Location
import Choreography.Choreo
import Control.Concurrent.Async
import System.Environment
import Data.Proxy
import Control.Monad.Identity (Identity(..), runIdentity, void)
import "freer-simple" Control.Monad.Freer as S
import "HasChor" Control.Monad.Freer (interpFreer, toFreer)

import Choreography.Location

import Data.Proxy
import Data.Time
import System.Environment
import GHC.TypeLits
import Control.Monad.Identity (Identity(..), runIdentity)
import "freer-simple" Control.Monad.Freer as S
import "HasChor" Control.Monad.Freer (interpFreer, toFreer)
import Flame.Principals
import Flame.TCB.Freer.IFC
import Flame.Assert

type Buyer = N "buyer"
buyer :: SPrin Buyer
buyer = SName (Proxy :: Proxy "buyer")

type Seller = N "seller"
seller :: SPrin Seller
seller = SName (Proxy :: Proxy "seller")

type BS = (Buyer \/ Seller)

bs :: SPrin BS
bs = (buyer *\/ seller)

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

labelIn :: l!(a @ loc) -> (l!a) @ loc
labelIn lal = wrap $ bind lal (label . unwrap)

labelIn' :: Monad m => Labeled m pc (l!(a @ loc)) -> Labeled m pc ((l!a) @ loc)
labelIn' e = e >>= (\lal -> wrap <$> (use lal (protect . unwrap)))

-- | Interpret the effects in a freer monad in terms of another monad.
wrapLabeled :: forall pc m a loc. Monad m => Labeled m pc a -> Labeled m pc (a @ loc)
wrapLabeled = Prelude.fmap wrap --- ???

labelOut :: (l!a) @ loc -> l!(a @ loc) 
labelOut lal = bind (unwrap lal) (label . wrap)

labelOut' :: (Monad m, l ⊑ l'', l' ⊑ l'') => Labeled m pc ((l!a) @ loc) -> Labeled m pc (l!(a @ loc))
labelOut' e = e >>= (\lal -> (use (unwrap lal) (protect . wrap)))

joinIn :: forall l l' l'' a loc. (l ⊑ l'', l' ⊑ l'') => l!((l'!a) @ loc) -> (l''!a) @ loc
joinIn = wrap . join . unwrap . labelIn

joinIn' :: forall l l' l'' pc m a loc. 
  (Monad m, l ⊑ l'', l' ⊑ l'') => Labeled m pc (l!((l'!a) @ loc)) -> Labeled m pc ((l''!a) @ loc)
joinIn' lx = wrap <$> do 
  x <- lx 
  let x' = (joinIn @l @l' @l'' x) -- why didn't this get inferred?
  use (unwrap x') protect

joinOut :: forall l l' l'' a loc. (l ⊑ l'', l' ⊑ l'') => l!((l'!a) @ loc) -> l''!(a @ loc)
joinOut llal = bind llal (\lal -> bind (unwrap lal) $ label . wrap)

-- | Perform a local computation at a given location.
slocally :: forall pc loc_pc l loc m a. (Monad m, KnownSymbol loc, pc ⊑ loc_pc, pc ⊑ l)
               => (SPrin pc, SPrin (N loc), SPrin loc_pc, SPrin l)
               -> (Unwrap loc -> Labeled m loc_pc (l!a))
               -> Labeled (Choreo m) pc ((l!a) @ loc)
slocally (pc, loc, loc_pc, l) k = do
  result <- restrict pc (\_ -> locally (sym loc) $ (\un -> runLabeled $ k un))
  return $ labelIn (joinOut result)


(~>:) :: (Show a, Read a, KnownSymbol loc, KnownSymbol loc') --, (N loc') ≽ (C pc), (N loc) ≽ (I pc))
     => (Proxy loc, SPrin pc, SPrin l, (l!a) @ loc)  
                                -- a sender's location, 
                                --a clearance, 
                                -- and a value located at the sender
     -> Proxy loc'-- ^ A receiver's location.
     -> Labeled (Choreo m) pc ((pc!(l!a)) @ loc')
(~>:) (loc, pc, l, la) loc' = do
  result <- restrict pc (\_ -> ((loc, la) ~> loc'))
  return $ labelIn result

-- | Conditionally execute choreographies based on a located value.
s_cond ::  forall pc l loc m a b. (Show a, Read a, KnownSymbol loc, pc ⊑ l)
     => (Proxy loc, SPrin pc, (a @ loc)) -- ^ A pair of a location and a scrutinee located on
                                         -- it.
     -> (a -> Labeled (Choreo m) pc b) -- ^ A function that describes the follow-up
                          -- choreographies based on the value of scrutinee.
     -> Labeled (Choreo m) pc (l!b)
s_cond (l, pc, la) c = restrict pc $ \_ -> cond (l, la) (\la -> runLabeled $ c la)


s_putStrLn :: Show a => SPrin pc -> (l ⊑ pc) => l!a -> Labeled IO pc (pc!())
s_putStrLn pc la = restrict pc (\open -> putStrLn (show $ open la))

s_getLine :: SPrin pc -> Labeled IO pc (pc!String)
s_getLine pc = restrict pc (\_ -> getLine)

safePutStrLn :: forall l a. (Show a, l ⊑ BS) => l!a 
                      -> Labeled IO BS (BS!())
safePutStrLn =  s_putStrLn bs

buyerGetLine :: Labeled IO FromBuyer (FromBuyer!String)
buyerGetLine = s_getLine fromBuyer

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
    use @_ @_ @_ @BS (join @_ @_ @BS (un title')) (\t -> protect $ priceOf t))
  -- the seller sends back the price of the book to the buyer
  price' <- ((sym seller, bs, fromSeller, price) ~>: sym buyer)
 
  -- the buyer decides whether to buy the book or not
  decision <- (bs, buyer, bs, fromBuyer) `slocally` (\un -> do
    use @_ @_ @_ @BS (join @_ @_ @BS (un price')) (\p -> protect (p < budget)))
 
  -- if the buyer decides to buy the book, the seller sends the delivery date to the buyer
  labelIn' (s_cond (sym buyer, bs, decision) $ (\d -> labelIn' $ use d (\case
    True  -> do
      deliveryDate  <- (bs, seller, bs, fromSeller) `slocally` (\un -> do
        use @_ @_ @_ @BS (join (un title')) (\t -> protect $ deliveryDateOf t))
      deliveryDate' <- ((sym seller, bs, fromSeller, deliveryDate) ~>: sym buyer)
 
      labelOut' ((bs, buyer, bs, fromBuyer) `slocally` (\un -> do
        use (join (un deliveryDate')) 
          (\dd -> do
            safePutStrLn $ label ("The book will be delivered on " ++ show dd)
            protect $ Just dd)))
 
    False -> labelOut' ((bs, buyer, bs, fromBuyer) `slocally` (\un -> do
        safePutStrLn $ label "The book's price is out of the budget"
        protect Nothing))
        )))

{- 
---- `bookseller'` is a simplified version of `bookseller` that utilizes `~~>`
--bookseller' :: Choreo IO (Maybe Day @ "buyer")
--bookseller' = do
--  title <- (buyer, \_ -> do
--               putStrLn "Enter the title of the book to buy"
--               getLine
--           )
--           ~~> seller
--
--  price <- (sym seller, \un -> return $ priceOf (un title)) ~~> (sym buyer)
--
--  cond' (sym buyer, \un -> return $ (un price) < budget) \case
--    True  -> do
--      deliveryDate <- (sym seller, \un -> return $ deliveryDateOf (un title)) ~~> (sym buyer)
--
--      (sym buyer) `locally` \un -> do
--        putStrLn $ "The book will be delivered on " ++ show (un deliveryDate)
--        return $ Just (un deliveryDate)
--
--    False -> do
--      (sym buyer) `locally` \_ -> do
--        putStrLn "The book's price is out of the budget"
--        return Nothing
-}

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
  case loc of
    "buyer"  -> runChoreography cfg (runLabeled bookseller) "buyer"
    "seller" -> runChoreography cfg (runLabeled bookseller) "seller"
  return ()
  where
    cfg = mkHttpConfig [ ("buyer",  ("localhost", 4242))
                       , ("seller", ("localhost", 4343))
                       ]

--main :: IO ()
---main = undefined