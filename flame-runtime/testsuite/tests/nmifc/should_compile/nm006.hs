{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}
module ShouldSucceed where

import Flame.Principals
import Flame.Runtime.Principals
import Flame.IFC 

six :: FLA m e n => SPrin p -> SPrin q -> m e n (I q) (p ∧ C q) a -> m e n (I q) (p ∧ q) a
six p q v = assume (p ≽ (q*←)) (reprotect v)
{- #6 this is badreceive from Commitment.hs -}
{- Fails (as desired)
nm_six :: (BFLA c m e n, p ⊑ Δ p) =>
                 SPrin p
                 -> SPrin q
                 -> c m e n (Δ p) (I q) (p ∧ C q) a
                 -> c m e n (Δ p) (I q) (p ∧ q) a
nm_six p q v = iassume ((p*←) ≽ (q*←)) (reprotect_b v)
-}

