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

{- #2 -}
nm_two :: (BFLA c m e n, q ⊑ Δ q) => SPrin p -> SPrin q
       -> c m e n (Δ q) (I p) (C p ∧ (I (p ∨ q))) a
       -> c m e n (Δ q) (I p) p a
nm_two p q v = iassume ((q*←) ≽ (p*←)) (reprotect_b v)
