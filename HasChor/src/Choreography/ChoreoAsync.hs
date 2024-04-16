{-# LANGUAGE GADTs              #-}
{-# LANGUAGE ImpredicativeTypes #-}

-- | This module defines `Choreo`, the monad for writing choreographies.
module Choreography.ChoreoAsync where

import Control.Concurrent.Async
import Choreography.Location
import Choreography.NetworkAsync
import Control.Monad.Freer
import Data.List
import Data.Proxy
import GHC.TypeLits
import Control.Monad.IO.Class
import Control.Monad.State hiding (lift)
import Control.Monad.State qualified as S

----------------------------------------------------------------------
-- * The Choreo monad

-- | A constrained version of `unwrap` that only unwraps values
-- located at a specific location.
type Unwrap l = forall a. a @ l -> a

-- | Effect signature for the `Choreo` monad. @m@ is a monad that
-- represents local computations.
data ChoreoSig m a where
  Local :: (KnownSymbol l)
        => Proxy l
        -> (Unwrap l -> m a)
        -> ChoreoSig m (a @ l)
  Comm :: (Show a, Read a, KnownSymbol l, KnownSymbol l')
       => Proxy l
       -> a @ l
       -> Proxy l'
       -> ChoreoSig m (Async a @ l')

  Cond :: (Show a, Read a, KnownSymbol l)
       => Proxy l
       -> a @ l
       -> (Async a -> Choreo m b) 
       -> ChoreoSig m b

  Broadcast :: (Show a, Read a, KnownSymbol l)
       => Proxy l
       -> a @ l
       -> ChoreoSig m (Async a)
     
 --data NetworkSig m a where
 --Lift   :: m a -> NetworkSig m a
 --Send   :: (Show a) => a -> SeqId -> LocTm -> NetworkSig m (Async Bool)
 --BCast :: (Show a) => a -> SeqId -> NetworkSig m ()
 --Recv   :: (Read a) => LocTm -> SeqId -> NetworkSig m (Async a) 

-- | Monad for writing choreographies.
type Choreo m = Freer (ChoreoSig m)

----------------------------------------------------------------------
-- * Endpoint projection

epp :: (MonadIO m) => Choreo m a -> LocTm -> Network m a
epp c l' = evalStateT (interpFreer handler c) 0
  where
    --handler :: ChoreoSig m a -> Network m a
    handler :: (MonadIO m) => ChoreoSig m a -> StateT Int (Network m) a
    handler (Local l m)
      | toLocTm l == l' = S.lift (wrap <$> lift (m unwrap))
      | otherwise       = S.lift (return Empty)
    handler (Comm s a r)
      | toLocTm s == toLocTm r = inc >> S.lift (lift $ liftIO $ wrap <$> async (return (unwrap a)))
      | toLocTm s == l'        = inc >>= \n ->  S.lift (send (unwrap a) n (toLocTm r) >> return Empty)
      | toLocTm r == l'        = inc >>= \n -> S.lift (wrap <$> recv (toLocTm s) n)
      | otherwise              = inc >> S.lift (return Empty)
    handler (Cond l a c) 
      | toLocTm l /= l' = inc >>= \n -> S.lift ((recv (toLocTm l) n) >>= \x -> epp (c x) l')
      | otherwise = inc >>= \n -> S.lift $ broadcast (unwrap a) n >>  do 
                                                                        as <- lift $ liftIO $ async (return $ unwrap a)
                                                                        epp (c as) l'
    handler (Broadcast l a)  
      | toLocTm l == l' = inc >>= \n -> S.lift $ broadcast (unwrap a) n  >> (lift $ liftIO $ async (return (unwrap a)))
      | otherwise = inc >>= \n -> S.lift ((recv (toLocTm l) n))

      --  where asy =  async (return $ unwrap a)
      --recv (toLocTm l) >>= \x -> epp (c x) l'
    inc :: (Monad m) => StateT Int m Int
    inc = do
      n <- get
      put (n + 1)
      return n

----------------------------------------------------------------------
-- * Choreo operations

-- | Perform a local computation at a given location.
locally :: KnownSymbol l
        => Proxy l           -- ^ Location performing the local computation.
        -> (Unwrap l -> m a) -- ^ The local computation given a constrained
                             -- unwrap funciton.
        -> Choreo m (a @ l)
locally l m = toFreer (Local l m)

cond :: (Show a, Read a, KnownSymbol l)
     => (Proxy l, a @ l)  -- ^ A pair of a location and a scrutinee located on
                          -- it.
     -> (Async a -> Choreo m b) -- ^ A function that describes the follow-up
                          -- choreographies based on the value of scrutinee.
     -> Choreo m b    
cond (l, a) c = toFreer (Cond l a c)

broad :: (Show a, Read a, KnownSymbol l)
     => (Proxy l, a @ l)  -- ^ A pair of a location and a scrutinee located on
                          -- it.
     -> Choreo m (Async a)
broad (l, a) = toFreer (Broadcast l a)

-- | Communication between a sender and a receiver.
(~>) :: (Show a, Read a, KnownSymbol l, KnownSymbol l')
     => (Proxy l, a @ l)  -- ^ A pair of a sender's location and a value located
                          -- at the sender
     -> Proxy l'          -- ^ A receiver's location.
     -> Choreo m (Async a @ l')
(~>) (l, a) l' = toFreer (Comm l a l')

-- | Run a choreography with a message transport backend.
runChoreography :: (Backend config, MonadIO m) => config -> Choreo m a -> LocTm -> m a
runChoreography cfg choreo l = runNetwork cfg l (epp choreo l)
