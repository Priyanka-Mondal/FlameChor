{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE ExplicitNamespaces #-}

module Main where

--import MyHasChor.Choreography
import MyHasChor.Choreography.Location
import MyHasChor.Choreography.NetworkAsync
import MyHasChor.Choreography.NetworkAsync.Http
import MyHasChor.Choreography.ChoreoAsync
import Control.Concurrent.Async
import MyHasChor.Choreography.Flaqr
import MyHasChor.Choreography.LabelledAsync
import System.Environment
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


-- locA :: Proxy "A"
-- locA = Proxy

-- locB :: Proxy "B"
-- locB = Proxy

-- locC :: Proxy "C"
-- locC = Proxy

-- client :: Proxy "client"
-- client = Proxy 

type A = N "A"
locA :: SPrin A
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


type AB = A \/ B
type BC = AB \/ D
type ABC = A \/ Client 
   --deriving (Show)

ab :: SPrin AB
ab = locA *\/ locB

bc :: SPrin BC
bc = ab *\/ locC

abc :: SPrin ABC
abc = locA *\/ client

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

type FrmClient = Client
frmClient :: SPrin Client
frmClient = client


safePutStrLn :: forall l a. (Show a, l ⊑ ABC) => l!a 
                      -> Labeled IO ABC (ABC!())
safePutStrLn =  sPutStrLn  abc

sfePutStrLn :: forall l a. (Show a, l ⊑ Client) => l!a 
                      -> Labeled IO Client (Client!())
sfePutStrLn =  sPutStrLn  client

aGetLine :: Labeled IO FromA (FromA ! Int)
aGetLine = strGetLine fromA

bGetLine :: Labeled IO FromB (FromB ! Int)
bGetLine = strGetLine fromB

cGetLine :: Labeled IO FromC (FromC ! Int)
cGetLine = strGetLine fromB
--------------
--------------
labelInA' :: l!(Async a @ loc) -> Async (l!a) @ loc
labelInA' (Seal asl) = case asl of
                        Wrap as -> Wrap $ Prelude.fmap Seal as
                        Empty   -> Empty

joinLoc :: forall l l' l'' loc a. (l ⊑ l'', l' ⊑ l'') => (l!(l'!a)) @ loc -> (l''!a) @ loc
joinLoc (Wrap lla) = Wrap $ join lla
joinLoc Empty      = Empty

labelin' :: l!(a @ loc) -> (l!a) @ loc
labelin' (Seal asl) = case asl of
                        Wrap as -> Wrap $ Seal as
                        Empty   -> Empty

labelIn'' :: l!(a @ loc) -> (l!a) @ loc
labelIn'' (Seal asl) = case asl of
                        Wrap as -> Wrap $ Seal as
                        Empty   -> Empty
-- socally :: forall pc loc_pc l loc m a. (Monad m, KnownSymbol loc, pc ⊑ loc_pc, pc ⊑ l)
--                => (SPrin pc, SPrin (N loc), SPrin loc_pc, SPrin l)
--                -> (Unwrap loc -> Labeled m loc_pc (l!a))
--                -> Labeled (Choreo m) pc ((l!a) @ loc)
-- socally (pc, loc, loc_pc, l) k = do
--   result <- restrict pc (\_ -> locally (sym loc) (\un -> runLabeled $ k un))
--   return $ joinLoc (labelIn'' result)

majorityQuorum :: Labeled (Choreo IO) Client ((Client ! ())  @ "client")
majorityQuorum = do 
 
  sLocally @Client @_ @Client @_ (client, client, client, frmClient) (\_ -> do
             sfePutStrLn @Client $ label @Client "at client$")

  --client `locally` \_ -> do putStrLn "at client$"

  -- a <- (abc, locA, abc, fromA) `sLocally` (\_ -> do
  --            safePutStrLn @ABC $ label "Enter value at A::"
  --            relabel' abc aGetLine)

  -- b <- (abc, locB, abc, fromB) `sLocally` (\_ -> do
  --            safePutStrLn @ABC $ label "Enter value at B::"
  --            relabel' abc bGetLine)

  -- c <- (abc, locC, abc, fromC) `sLocally` (\_ -> do
  --            safePutStrLn @ABC $ label "Enter value at C::"
  --            relabel' abc cGetLine)

  --a' <- (sym locA, abc, fromA, a) ~>: sym client
  -- b' <- (sym locB, abc, fromB, b) ~>: sym client
  -- c' <- (sym locC, abc, fromC, c) ~>: sym client

  -- cc <- (abc, client, abc, abc) `sLocally` \un -> do
  --             title'' <- join @ABC . join @ABC <$> restrict @ABC abc (\_ -> wait (un a'))
  --             use @_ @ABC  title'' (protect @_ @ABC. times3)

  -- (abc, client, abc, fromClient) `sLocally` \un -> do
  --             let c'' = un c
  --             use c'' (\y -> protect (do 
  --                 let r = restrict abc (\_ -> wait y)
  --                 let title'' = join <$> r
  --                 t <- title''
  --                 use t (protect . times3)))
  -- clientc <- (abc, client, abc, fromClient) `sLocally` \un -> do
  --     (c'' :: ABC!Int) <- join . join @_ @_ @ABC <$> restrict @_ @_ @ABC abc (\_ -> wait (un c'))
  --     use @_ @_ @_ @ABC c'' (protect . times3)
   

  -- (abc, client, abc, fromClient) `sLocally` (\un -> do
  --            safePutStrLn @ABC $ label $ un cc)
  
  -- (abc, client, abc, fromClient) `sLocally` \un -> do
  --     (c'' :: ABC!Int) <- join . join @_ @_ @ABC <$> restrict @_ @_ @ABC abc (\_ -> wait (un a'))
  --     use @_ @_ @_ @ABC c'' (protect . times3)

  -- (abc, client, abc, abc) `sLocally` \un -> do
  --             title'' <- join . join <$> restrict abc (\_ -> wait (un c'))
  --             use title'' (protect . times3)

  --return price

  -- price <- (abc, client, abc, fromClient) `sLocally` (\un -> do
  --   use @_ @_ @_ @ABC (join (asyncWait a')) (\t -> do
  --                                     z <- wait t
  --                                     protect $ times3 t))
  {--
  -- title is (BS ! (BS ! String)) @ seller
  --  price <- (bs, seller, bs, fromSeller) `slocally` (\un -> do
  --   use @_ @_ @_ @BS (join @_ @_ @BS (un title')) (\t -> protect $ priceOf t))
  -- abc <- (abc, client, abc, fromClient) `sLocallyAsync` \un -> do 
  --   relabel' abc $ selecT $ compare_ [un a', un b', un c'] 2
--Expected: Labeled IO pc'0 (l0 ! (FromClient ! Int))
--    Actual: IO (Async a0)
  m <- client `locally` \un -> do
    q <- wait (un abc)
    print q
    return q

  ma <- (client,m) ~> locA
  mb <- (client, m) ~> locB
  mc <- (client, m) ~> locC

  locA `locally` \un -> do
    q <- wait (un ma)
    print q

  locB `locally` \un -> do
    q <- wait (un mb)
    print q

  locC `locally` \un -> do
    q <- wait (un mc)
    print q

  --bc <- client `locally` \un -> do compare (un b') (un c')
  --ca <- client `locally` \un -> do compare (un c') (un a')
  --bcca <- client `locally` \un -> do select (un bc) (un ca)
  --abc <- client `locally` \un -> do select (un ab) (un bcca)
  client `locally` \_ -> do 
      putStrLn "consensus done"
      getLine
  return abc
  --}


majorityQuorumMain :: IO ()
majorityQuorumMain = do
  [loc] <- getArgs
  -- Labeled (Choreo IO) ABC ((ABC ! Int)  @ "client")
  case loc of
    "client" -> runChoreography cfg (runLabeled  majorityQuorum) "client"
    "A" -> runChoreography cfg (runLabeled  majorityQuorum) "client"
    "B" -> runChoreography cfg (runLabeled  majorityQuorum) "client"
    "C" -> runChoreography cfg (runLabeled  majorityQuorum) "client"
  return ()
  where
    cfg = mkHttpConfig [ ("A", ("localhost", 4240))
                       , ("B", ("localhost", 4341))
                       , ("C", ("localhost", 4544))
                       , ("client", ("localhost", 4445))
                       ]
----------------------------------------------------------------------
-- Entry point

times3 :: Int -> Int
times3 x = 3*x 

main = majorityQuorumMain