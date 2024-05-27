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

{- #7 this is similar to badreceive -}
nm_seven :: (BFLA c m e n) =>
                 SPrin p
                 -> SPrin q
                 -> c m e n (Δ q) (I p) (C p ∧ I q) a
                 -> c m e n (Δ q) (I p) (p ∧ I q) a
nm_seven p q v = iassume ((q*←) ≽ (p*←)) (reprotect_b v)
