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

{- #12 -}
twelve :: (FLA m e n, r ≽ q) =>
          SPrin p
          -> SPrin q
          -> SPrin r
          -> m e n ((∇) p) (I p ∧ q) a
          -> m e n ((∇) p) ((I p) ∧ (I q) ∧ (C r)) a
twelve p q r v = reprotect v
nm_twelve :: (BFLA c m e n, r ≽ q) =>
           SPrin p
           -> SPrin q
           -> SPrin r
           -> c m e n (C q) ((∇) p) (I p ∧ q) a
           -> c m e n (C q) ((∇) p) ((I p) ∧ (I q) ∧ (C r)) a
nm_twelve p q r v = reprotect_b v

