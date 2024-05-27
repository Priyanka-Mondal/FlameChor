{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

import Flame.Principals
import Flame.IFC

doit :: SPrin l -> Lbl l a -> FLAC IO pc (pc ⊔ l) a
doit = undefined

test :: (client === client') =>  SPrin client -> SPrin client' -> FLAC IO client client ()
test client client' = reprotect $ doit client' (label ())

main :: IO (Lbl KTop ())
main = runFLAC $ test STop STop
