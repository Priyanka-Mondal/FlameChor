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

one :: FLA m e n => SPrin p -> SPrin q
       -> m e n (I q) (C p ∧ (I (p ∨ q))) a
       -> m e n (I q) (C p ∧ I q) a
one p q v = assume ((p*←) ≽ (q*←)) (reprotect v)

{- #1 -}                             
nm_one :: (BFLA c m e n, p ⊑ Δ p) =>
       SPrin p -> SPrin q
       -> c m e n (Δ p) (I q) (C p ∧ (I (p ∨ q))) a
       -> c m e n (Δ p) (I q) (C p ∧ I q) a
nm_one p q v = iassume ((p*←) ≽ (q*←)) (reprotect_b v)

