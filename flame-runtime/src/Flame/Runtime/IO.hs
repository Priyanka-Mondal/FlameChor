{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- {-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Flame.Runtime.IO
       {- TODO: interface -}
where
  
import Flame.Principals
import Flame.TCB.IFC 
import qualified System.IO as SIO
import qualified Control.Monad.IO.Class as MIO

data IFCHandle (l::KPrin) = NewHdl { unsafeUnwrap :: SIO.Handle }

mkStdout :: SPrin out -> IFCHandle out
mkStdout out = NewHdl SIO.stdout
mkStderr :: SPrin err -> IFCHandle err
mkStderr err = NewHdl SIO.stderr
mkStdin  :: SPrin in_ -> IFCHandle in_
mkStdin in_ = NewHdl SIO.stdin

hFlush :: (IFC m IO n, pc ⊑ l) => IFCHandle l -> m IO n pc l' ()
hFlush h = unsafeProtect $ do
  _ <- SIO.hFlush (unsafeUnwrap h)
  return $ label ()

hPrint :: (IFC m IO n, Show a, pc ⊑ l) => IFCHandle l -> a -> m IO n pc l' ()
hPrint h s = unsafeProtect $ do
  _ <- SIO.hPrint (unsafeUnwrap h) s
  return $ label ()

hPutChar :: (IFC m IO n, pc ⊑ l) => IFCHandle l -> Char -> m IO n pc l' ()
hPutChar h c = unsafeProtect $ do
  _ <- SIO.hPutChar (unsafeUnwrap h) c
  return $ label ()

hPutStr :: (IFC m IO n, pc ⊑ l) => IFCHandle l -> String -> m IO n pc l' ()
hPutStr h s = unsafeProtect $ do
  _ <- SIO.hPutStr (unsafeUnwrap h) s
  return $ label ()

hPutStrLn :: (IFC m IO n, pc ⊑ l) => IFCHandle l -> String -> m IO n pc l' ()
hPutStrLn h s = unsafeProtect $ do
  _ <- SIO.hPutStrLn (unsafeUnwrap h) s
  return $ label ()

hGetChar :: IFC m IO n => IFCHandle l -> m IO n pc l Char
hGetChar h = unsafeProtect $ do
  c <- SIO.hGetChar (unsafeUnwrap h)
  return $ label c

hGetLine :: IFC m IO n => IFCHandle l -> m IO n pc l String
hGetLine h = unsafeProtect $ do
  s <- SIO.hGetLine (unsafeUnwrap h)
  return $ label s

class (IFC m e n, IFC m IO n) => IFCIO m e n where
  liftIO :: m IO n pc l a -> m e n pc l a

instance (MIO.MonadIO e, IFC m e n, IFC m IO n) => IFCIO m e n where
  liftIO a = unsafeProtect $ MIO.liftIO $ runIFC a