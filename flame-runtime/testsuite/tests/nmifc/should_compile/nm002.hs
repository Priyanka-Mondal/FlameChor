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

two :: FLA m e n => SPrin p -> SPrin q
       -> m e n (I p) (C p ∧ (I (p ∨ q))) a
       -> m e n (I p) p a
two p q v = assume ((q*←) ≽ (p*←)) (reprotect v)

{- #2 -}
{- Fails (as desired): "Could not deduce (C (Δ q) ≽ C (C p ∧ I (p ∨ q)))"
nm_two :: (BFLA c m e n, q ⊑ Δ q) => SPrin p -> SPrin q
       -> c m e n (Δ q) (I p) (C p ∧ (I (p ∨ q))) a
       -> c m e n (Δ q) (I p) p a
nm_two p q v = iassume ((q*←) ≽ (p*←)) (reprotect_b v)
-}
