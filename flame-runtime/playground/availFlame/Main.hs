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
import MyHasChor.Choreography.Flaqr
import Data.Proxy
import Data.Time
import System.Timeout 
import System.Environment
import GHC.TypeLits

import Flame.Principals
import Flame.TCB.Freer.IFC

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

-- joinLoc' :: forall l l' l'' loc a. (l ⊑ l') => (l!a) @ loc -> (l'!a) @ loc
-- joinLoc' = joinLoc

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

largest ::forall l l' l'' a. (HasFail a, Eq a, l ⊑ l'', l' ⊑ l'', Show a, Ord a) => 
    Async (l!(l'!a)) -> Async (l!(l'!a)) -> IO (Async (l!(l'!a)))
largest a b = do 
 z <- timeout 10000000 (waitBoth a b)
 case z of 
  Nothing -> async (return $ Seal (Seal failVal))
  Just (x,y) -> do 
    let a1 = join x
    let b1 = join y
    case (a1, b1) of 
      (Seal a1', Seal b1') -> if a1' > b1' then return a --async (return a1)
                              else return b --async (return b1) 
      _ -> async (return $ Seal (Seal failVal))

                            


sSelect :: forall l l' l'' a. (HasFail a, Eq a, l ⊑ l'', l' ⊑ l'', Show a) => 
    Async (l!(l'!a)) -> Async (l!(l'!a)) -> IO (Async (l!(l'!a)))
sSelect a b = do
    a' <- timeout time (wait a)
    case a' of 
      (Just e) -> do 
        let e1 = join e
        case e1 of 
          Seal c | c /= failVal -> do 
            return a --async (return e1)
          _ -> do 
                b' <- timeout time (wait b)
                case b' of 
                  (Just e) -> do
                    let b1 = join e
                    return b -- async (return b1) 
                  Nothing -> async (return (Seal (Seal failVal)))
      _ -> do -- Nothing i.e. a did not arrive
         b' <- timeout time (wait b)
         case b' of 
          (Just e) -> do 
            let b1' = join e
            return b -- async( return b1')
          Nothing -> do 
            async (return (Seal (Seal failVal)))

bsSelect :: (HasFail a, Eq a, BS ⊑ BS) => 
    Async (BS!(BS!a)) -> Async (BS!(BS!a)) -> IO (Async (BS!a))
bsSelect a b = do
    a' <- timeout time (wait a)
    case a' of 
      (Just e) -> do 
        let e1 = join e
        case e1 of 
          Seal c | c /= failVal -> async (return e1)
          _ -> do 
                b' <- timeout time (wait b)
                case b' of 
                  (Just e) -> do
                    let b1 = join e
                    async (return b1) 
                  Nothing -> async (return (Seal failVal))
      _ -> do
         b' <- timeout time (wait b)
         case b' of 
          (Just e) -> do 
            let b1' = join e
            async( return b1')
          Nothing -> async (return (Seal failVal))


-- | `bookb1` is a choreography that implements the bookb1 protocol.
bookb1 :: Labeled (Choreo IO) BS ((BS ! (Int)) @ "client")
bookb1 = do
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

  largest <- (bs, client, bs, fromClient) `sLocally` \un -> do
          restrict @_ @_ @BS bs (\_ -> (do 
            largest @BS @BS @BS (un bal1') (un bal2') ))
          
  available <- (bs, client, bs, fromClient) `sLocally` \un -> do
       restrict @_ @_ @BS bs (\_ -> (do 
         sSelect @BS @BS @BS (un bal1') (un bal2')))
  
  larAvail <- (bs, client, bs, fromClient) `sLocally` \un -> do
    use @_ @BS @BS @BS (un largest) (\lar -> use @_ @BS @BS @BS (un available) (\avl -> --protect
      join. join @BS @BS @BS <$> restrict @_ @_ @BS bs (\_ ->
              (do 
                s <- sSelect @BS @BS @BS (lar) (avl)
                (wait s)))))--))
 
  (bs, b2, bs, fromB2) `sLocally` (\un -> do
             relabel' bs b2GetLine)
  
  (bs, b1, bs, fromB1) `sLocally` (\un -> do
             relabel' bs b1GetLine)

  (bs, client, bs, fromClient) `sLocally` \un -> do
              safePutStrLn @BS $ label "largest available balance:"
              safePutStrLn @BS $ (un larAvail)
              relabel' bs clientGetLine
 
  
  -- if the client decides to buy the book, the b1 sends the delivery date to the client
  
-- budget :: Int
-- budget = 100

-- priceOf :: String -> Int
-- priceOf "T" = 80
-- priceOf "H"            = 120

-- priceOf2 :: String -> Int
-- priceOf2 "T" = 90
-- priceOf2 "H"            = 100

-- largest :: (Int , Int) -> Int
-- largest (a ,b) = if (a > b) then a else b

-- deliveryDateOf :: String -> Day
-- deliveryDateOf "T" = fromGregorian 2022 12 19
-- deliveryDateOf "H" = fromGregorian 2023 01 01

main :: IO ()
main = do
  [loc] <- getArgs
  case loc of
    "client"  -> runChoreography cfg (runLabeled bookb1) "client"
    "b1" -> runChoreography cfg (runLabeled bookb1) "b1"
    "b2" -> runChoreography cfg (runLabeled bookb1) "b2"
  return ()
  where
    cfg = mkHttpConfig [ ("client",  ("localhost", 4242))
                       , ("b1", ("localhost", 4343))
                       , ("b2", ("localhost", 4344))
                       ]