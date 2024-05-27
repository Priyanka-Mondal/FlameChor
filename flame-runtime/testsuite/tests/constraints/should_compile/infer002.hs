{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module UnifyMe where

import Prelude hiding (print, putStr, putStrLn, getLine)

import Flame.Runtime.IO
import Flame.Principals
import Flame.IFC 
import Data.Proxy

{- A static principal for Alice -}
alice  = SName (Proxy :: Proxy "Alice")
type Alice = KName "Alice"

aliceSecret :: Lbl Alice String
aliceSecret = label "secret"

unifyMe :: Maybe a -> IO ()
unifyMe ma = let stdout = mkStdout (SBot*→) in
        do _ <- runFLAC @IO @Lbl @(I Alice) @KBot $
                  case ma of
                    Just a ->
                      {- Use the granted authority print Alice's secret -}
                      assume ((*∇) SBot ≽ (*∇) alice) $ assume (SBot ≽ alice) $
                        bind aliceSecret $ \secret ->
                        hPutStrLn stdout secret
                    Nothing ->             
                        hPutStrLn stdout "Incorrect password."
           return ()
