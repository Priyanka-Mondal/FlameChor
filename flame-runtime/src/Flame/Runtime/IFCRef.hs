{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
-- {-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Flame.Runtime.IFCRef
where

import Flame.Principals
import Flame.TCB.IFC 
import Data.IORef

data IFCRef (l::KPrin) a = IFCRef { unsafeUnwrap :: IORef a}

newIFCRef :: forall l pc m n a. (IFC m IO n, pc ⊑ l) => a -> m IO n pc pc (IFCRef l a)
newIFCRef a = unsafeProtect $ do 
                  r <- newIORef a
                  return . label $ IFCRef r

writeIFCRef :: (IFC m IO n, pc ⊑ l) => IFCRef l a -> a -> m IO n pc pc' ()
writeIFCRef ref a = unsafeProtect $ do 
                      writeIORef (unsafeUnwrap ref) a;
                      return . label $ ()

readIFCRef :: IFC m IO n => IFCRef l a -> m IO n pc (pc ⊔ l) a
readIFCRef ref = unsafeProtect $ do 
                   r <- readIORef (unsafeUnwrap ref)
                   return . label $ r
--modifyIORef :: IORef a -> (a -> a) -> IO ()
