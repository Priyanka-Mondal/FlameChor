{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}
module ShouldFail where

import Flame.Principals
import Flame.Runtime.Principals
import Flame.IFC 

{- #5 not allowed.  This endorsement is malleable. -}
nm_five :: BFLA c m e n => SPrin p 
       -> c m e n (Δ KBot) (I p) (C p) a
       -> c m e n (Δ KBot) (I p) p  a
nm_five p v = iassume (((SBot)*←) ≽ (p*←)) (reprotect_b v)
