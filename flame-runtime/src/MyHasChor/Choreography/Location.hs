{-# LANGUAGE DataKinds #-}
{-# LANGUAGE  RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE  KindSignatures #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | This module defines locations and located values.
module MyHasChor.Choreography.Location where

import Data.Proxy
import Data.String
import GHC.TypeLits
import Language.Haskell.TH

-- | Term-level locations.
type LocTm = String

-- | Type-level locations.
type LocTy = Symbol

-- | Convert a type-level location to a term-level location.
toLocTm :: forall (l :: LocTy). KnownSymbol l => Proxy l -> LocTm
toLocTm = symbolVal

-- | Located values.
--
-- @a \@ l@ represents a value of type @a@ at location @l@.
data a @ (l :: LocTy)
  = Wrap a -- ^ A located value @a \@ l@ from location @l@'s perspective.
  | Empty  -- ^ A located value @a \@ l@ from locations other than @l@'s
           -- perspective.

-- | Wrap a value as a located value.
wrap :: a -> a @ l
wrap = Wrap

-- | Unwrap a located value.
--
-- /Note:/ Unwrapping a empty located value will throw an exception.
unwrap :: a @ l-> a
unwrap (Wrap a) = a
unwrap Empty    = error "this should never happen for a well-typed choreography"

--sunwrap :: (s ! a) @ l -> s ! (a @ l)

-- pack back Empty 
-- (bob ! a ) @ l --> bob ! (a @ l) at l
--                    bob ! (Empty) when not at l

-- | Define a location at both type and term levels.
mkLoc :: String -> Q [Dec]
mkLoc loc = do
  let locName = mkName loc
  let p = mkName "Data.Proxy.Proxy"
  pure [SigD locName (AppT (ConT p) (LitT (StrTyLit loc))),ValD (VarP locName) (NormalB (ConE p)) []]
