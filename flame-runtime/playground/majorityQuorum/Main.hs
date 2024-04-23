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
import MyHasChor.Choreography.Flaqr
--import MyHasChor.Choreography.LabelledAsync
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


type ABC = (((A \/ B) \/ D) \/ Client )
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

ccompare :: forall l l' l'' a loc pc. (HasFail a, Show a, Read a, KnownSymbol loc, Eq a) =>
  (SPrin (N loc), SPrin pc) ->  (Async (l!(l'!a))) @ loc -> (Async (l!(l'!a))) @ loc
  -> Labeled (Choreo IO) pc (pc ! (Async (l!(l'!a))) @ loc)
ccompare (loc, pc) a b = do 
    labelIn <$> restrict @pc @_ @pc pc (\_ -> do 
      locally (sym loc) (\un -> do
                                  let a' = un a
                                  a'' <- timeout time (wait a')
                                  case a'' of 
                                    (Just e) -> do
                                      let e1 = join e
                                      case e1 of 
                                        Seal c | c /= failVal -> do 
                                          let b' = un b
                                          b'' <- timeout time (wait b')
                                          case b'' of 
                                            (Just e') -> do 
                                              let e2 = join e' 
                                              case e2 of 
                                                Seal d | d /= failVal -> if d == c then return b' else async (return (Seal (Seal failVal)))
                                            Nothing -> async (return (Seal (Seal failVal)))
                                        _ -> async (return (Seal (Seal failVal)))
                                    Nothing -> async (return (Seal (Seal failVal)))
                        )
                )

sSelect :: forall l l' l'' a. (HasFail a, Eq a, Show a) => 
    Async (l!(l'!a)) -> Async (l!(l'!a)) -> IO (Async (l!(l'!a)))
sSelect a b = do
    a' <- timeout time (wait a)
    case a' of 
      (Just e) -> do 
        let e1 = join e
        case e1 of 
          Seal c | c /= failVal -> do 
            return a 
          _ -> do 
                b' <- timeout time (wait b)
                case b' of 
                  (Just e) -> do
                    let b1 = join e
                    return b 
                  Nothing -> async (return (Seal (Seal failVal)))
      _ -> do -- Nothing i.e. a did not arrive
         b' <- timeout time (wait b)
         case b' of 
          (Just e) -> do 
            let b1' = join e
            return b 
          Nothing -> do 
            async (return (Seal (Seal failVal)))



-- sSelect' :: forall l l' l'' a pc. (HasFail a, Eq a, Show a, pc ⊑ l, pc ⊑ l') => 
--     (SPrin pc) -> Async (l!(l'!a)) -> Async (l!(l'!a)) -> Labeled IO pc (pc ! Async (l!(l'!a)))
-- sSelect' pc a b = do
--     a' <- liftIO $ timeout time (wait a)
--     case a' of 
--       (Just e) -> do 
--         let e1 = join e
--         case e1 of 
--           Seal c | c /= failVal -> do 
--             restrict pc (\_ -> return a) 
--           _ -> do 
--                 b' <- liftIO $ timeout time (wait b)
--                 case b' of 
--                   (Just e) -> do
--                     --let b1 = join e
--                     restrict pc (\_ -> return b)
--                   Nothing -> restrict pc (\_ -> do async (return (Seal (Seal failVal))))
--       _ -> do -- Nothing i.e. a did not arrive
--          b' <- liftIO $ timeout time (wait b)
--          case b' of 
--           (Just e) -> do 
--             --let b1' = join e
--             restrict pc (\_ -> return b) 
--           Nothing -> do 
--             restrict pc (\_ -> async (return (Seal (Seal failVal))))

sCompare :: forall l l' l'' a. (HasFail a, Eq a, l ⊑ l'', l' ⊑ l'', Show a) => 
    Async (l!(l'!a)) -> Async (l!(l'!a)) -> IO (Async (l!(l'!a)))
sCompare a b = do
    a' <- timeout time (wait a)
    case a' of 
      (Just e) -> do
         let e1 = join e
         case e1 of 
           Seal c | c /= failVal -> do 
             b' <- timeout time (wait b)
             case b' of 
               (Just e') -> do 
                let e2 = join e' 
                case e2 of 
                  Seal d | d /= failVal -> if d == c then return b else async (return (Seal (Seal failVal)))
               Nothing -> async (return (Seal (Seal failVal)))
           _ -> async (return (Seal (Seal failVal)))
      Nothing -> async (return (Seal (Seal failVal)))


-- sCompare' :: forall l l' l'' a pc. (HasFail a, Eq a, pc ⊑ l, pc ⊑ l', Show a) => 
--      (SPrin pc) -> Async (l!(l'!a)) -> Async (l!(l'!a)) -> Labeled IO pc (pc ! Async (l!(l'!a)))
-- sCompare' pc a b = do
--     a' <- restrict @_ @_ @pc pc (\_ -> timeout time (wait a))
--     use @_ @_ @_ @_ a' (\a' -> do
--         case a' of 
--           (Just e) -> do
--             let e1 = join @_ @_ @_ e
--             case e1 of 
--               Seal c | c /= failVal -> do 
--                 b' <- restrict @_ @_ @pc pc (\_ -> timeout time (wait b))
--                 use @_ @_ @_ @_ b' (\b' -> do
--                   case b' of 
--                     (Just e') -> do 
--                       let e2 = join @_ @_ @pc e' 
--                       case e2 of 
--                         Seal d | d /= failVal -> if d == c then (restrict pc (\_ -> return b)) else (restrict pc (\_ -> do async (return (Seal (Seal failVal)))))
--                     Nothing -> restrict pc (\_ -> do async (return (Seal (Seal failVal)))))
--               _ -> restrict pc  (\_ -> do async (return (Seal (Seal failVal))))
--           Nothing -> restrict pc  (\_ -> do async (return (Seal (Seal failVal))))
--                               )


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
  
 

  -- sWait on a b c client locally
  -- ABC ! (Maybe), 

  -- ab <- (abc, client, abc, fromClient) `sLocally` \un -> do
  --       a'' <- sWait a'
  --       b'' <- sWait b'
  --       c'' <- sWait c'  
  --       sSelect (sCompare a'' b'') (sSelect (sCompare b'' c'') (sCompare ))
  -- moving restrict inside
  -- typeclass that abstarcts away the difference between Async and FailOr 

  -- ab <- (abc, client, abc, fromClient) `sLocally` \un -> do
  --      restrict @_ @_ @ABC abc (\_ -> (do 
  --        sCompare @_ @_ @ABC (un a') (un b')))
  

  -- bc <- (abc, client, abc, fromClient) `sLocally` \un -> do
  --      restrict @_ @_ @ABC abc (\_ -> (do 
  --        sCompare @_ @_ @ABC (un b') (un c')))

  -- ca <- (abc, client, abc, fromClient) `sLocally` \un -> do
  --       restrict @_ @_ @ABC abc (\_ -> (do 
  --        sCompare @_ @_ @ABC (un c') (un a')))

  ab <- ccompare (client, abc) a' b'
  bc <- ccompare (client, abc) b' c'
  ca <- ccompare (client, abc) c' a'
  
  abc' <- (abc, client, abc, fromClient) `sLocally` \un -> do
    use @_ @ABC @ABC @ABC (un ab) (\ab -> use @_ @ABC @ABC @ABC (un bc) (\bc -> 
      restrict @_ @_ @ABC abc (\_ -> do
              (sSelect @ABC @ABC @ABC (ab) (bc)
                )))) 

  con <- (abc, client, abc, fromClient) `sLocally` \un -> do
    use @_ @ABC @ABC @ABC (un ca) (\ca -> use @_ @ABC @ABC @ABC (un abc') (\abc' -> 
      join. join @ABC @ABC @ABC <$> restrict @_ @_ @ABC abc (\_ ->
              (do 
                s <- sSelect @ABC @ABC @ABC (ca) (abc')
                (wait s)))))
  
  -- a <- (abc, locA, abc, fromA) `sLocally` (\_ -> do
  --            relabel' abc aGetLine)

  -- b <- (abc, locB, abc, fromB) `sLocally` (\_ -> do
  --            relabel' abc bGetLine)

  -- c <- (abc, locC, abc, fromC) `sLocally` (\_ -> do
  --            relabel' abc cGetLine)
 
  -- sWait 
  (abc, client, abc, fromClient) `sLocally` \un -> do
              safePutStrLn @ABC $ label "value after consensus:"
              safePutStrLn @ABC $ (un con)

-- quorumMain :: HttpConfig -> IO () -- this one needs A B and C to run until Client performs wait()
-- quorumMain cfg = do
--   [loc] <- getArgs
--   case loc of
--     "client" -> runChoreography cfg (runLabeled  majorityQuorum) "client"
--     "A" -> runChoreography cfg (runLabeled  majorityQuorum) "A"
--     "B" -> runChoreography cfg (runLabeled  majorityQuorum) "B"
--     "C" -> runChoreography cfg (runLabeled  majorityQuorum) "C"
--   return ()


quorumMain :: HttpConfig -> IO ()
quorumMain cfg = do
  [loc] <- getArgs
  runChoreography cfg (runLabeled  majorityQuorum) loc >> return () >> quorumMain cfg
 
main = do 
  quorumMain cfg 
 where
    cfg = mkHttpConfig [ ("A", ("localhost", 4242))
                       , ("B", ("localhost", 4343))
                       , ("C", ("localhost", 4544))
                       , ("client", ("localhost", 4546))
                       ]

--main = majorityQuorumMain