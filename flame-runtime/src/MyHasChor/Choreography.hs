{-# LANGUAGE ExplicitNamespaces #-}

-- | This module defines the interface to HasChor. The client of the library is
-- highly recommended to only use constructs exported by this module.
module MyHasChor.Choreography (
  -- * Locations and Located Values
  LocTm,
  LocTy,
  type (@),
  mkLoc,
  -- * The Choreo monad
  Choreo,
  -- ** Choreo operations
  locally,
  (~>),
  (~~>),
  cond,
  cond',

  -- * Message transport backends
  -- ** The HTTP backend
  Host,
  Port,
  HttpConfig,
   mkHttpConfig,

  -- * Running choreographies
  runChoreo,
  runChoreography
  ) where

import MyHasChor.Choreography.Location
import MyHasChor.Choreography.Choreo
import MyHasChor.Choreography.Network
import MyHasChor.Choreography.Network.Http
import MyHasChor.Choreography.Network.Local
import Control.Monad.IO.Class
import Data.Proxy
import MyHasChor.Choreography.Flaqr

-- | Run a choreography with a message transport backend.
runChoreography :: (Backend config, MonadIO m) => config -> Choreo m a -> LocTm -> m a
runChoreography cfg choreo l = runNetwork cfg l (epp choreo l)
