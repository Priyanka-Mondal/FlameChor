{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

import Prelude hiding (print, putStr, putStrLn, getLine)

import Flame.Runtime.IO
import Flame.Principals
import Flame.IFC 
import Data.Proxy

{- A static principal for Alice -}
alice  = SName (Proxy :: Proxy "Alice")
type Alice = KName "Alice"

inputPass :: SPrin client
            -> IFCHandle (I client)
            -> IFCHandle (C client)
            -> FLAC IO (I Alice) (I Alice) String
inputPass client stdin stdout = do
      {- Endorse the guess to have Alice's integrity -}
      reprotect $ hGetLine stdin

main = undefined
