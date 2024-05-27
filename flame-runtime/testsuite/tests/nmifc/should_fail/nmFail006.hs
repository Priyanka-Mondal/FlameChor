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

{- #6 this is badreceive from Commitment.hs -}
nm_six :: (BFLA c m e n, p ⊑ Δ p) =>
                 SPrin p
                 -> SPrin q
                 -> c m e n (Δ p) (I q) (p ∧ C q) a
                 -> c m e n (Δ p) (I q) (p ∧ q) a
nm_six p q v = iassume ((p*←) ≽ (q*←)) (reprotect_b v)
