{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module UnifyMe where

import Prelude hiding (print, putStr, putStrLn, getLine)

import Flame.Runtime.IO
import Flame.Principals
import Flame.IFC 
import Flame.Assert
import Data.Proxy
import Data.Type.Equality

topSecret :: Lbl KTop String
topSecret = label "secret"

unifyMe :: Maybe a -> IO ()
unifyMe ma = let stdout = mkStdout (SBot*→) in
        do _ <- runFLA $
                  case ma of
                    Just a ->
                      {- Use the granted authority print Top's secret -}
                      assume ((*∇) SBot ≽ (*∇) STop) $ assume (SBot ≽ STop) $
                        ebind topSecret $ \secret ->
                        -- this explicit application necessary because GHC does not
                        -- unify variables under implications.
                        -- This restriction means it is safe to unify principal kinded
                        -- type variables based on assume'd givens.
                        hPutStrLn @_ @Lbl @KBot @(C KBot) @KBot stdout secret
                    Nothing ->             
                        hPutStrLn @_ @Lbl @KBot @(C KBot) @KBot stdout "Incorrect password."
           return ()
