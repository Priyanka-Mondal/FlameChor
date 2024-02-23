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

{- #8 this is similar to battleship -}
eight :: FLA m e n =>
         SPrin p
      -> SPrin q
      -> m e n (I p) (C (p ∨ q) ∧ I q) a
      -> m e n (I p) (C (p ∨ q) ∧ I (p ∧ q)) a
eight p q v = assume (q ≽ (p*←)) (reprotect v)
nm_eight :: (BFLA c m e n, q ⊑ Δ q) =>
                 SPrin p
                 -> SPrin q
                 -> c m e n (Δ q) (I p) (C (p ∨ q) ∧ I q) a
                 -> c m e n (Δ q) (I p) (C (p ∨ q) ∧ I (p ∧ q)) a
nm_eight p q v = iassume ((q*←) ≽ (p*←)) (reprotect_b v)

