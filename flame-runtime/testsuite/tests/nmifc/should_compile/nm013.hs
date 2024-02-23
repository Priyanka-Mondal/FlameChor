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

{- #13 -}
thirteen :: (FLA m e n, q ⊑ r) =>
          SPrin p
          -> SPrin q
          -> SPrin r
          -> m e n pc (I p ∧ q) a
          -> m e n pc (I p ∧ r) a
thirteen p q r v = reprotect v
nm_thirteen :: (BFLA c m e n, q ⊑ r) =>
           SPrin p
           -> SPrin q
           -> SPrin r
           -> c m e n (C q) pc (I p ∧ q) a
           -> c m e n (C q) pc (I p ∧ r) a
nm_thirteen p q r v = reprotect_b v


