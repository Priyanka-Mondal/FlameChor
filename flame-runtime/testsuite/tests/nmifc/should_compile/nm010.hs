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

{- #10 is open from Commitment.hs -}
ten :: FLA m e n => SPrin p -> SPrin q -> m e n ((∇) p) (p ∧ (I q)) a -> m e n ((∇) p) ((I p) ∧ q) a
ten p q v = assume ((*∇) (q) ≽ (*∇) (p)) $ assume ((q*→) ≽ (p*→)) (reprotect v)

nm_ten :: (BFLA c m e n, p ~ N p', q ~ N q') =>
           SPrin p
           -> SPrin q
           -> c m e n (C (p ∨ q) ∧ I p ∧ ((∇) q)) ((∇) p) (p ∧ (I q)) a
           -> c m e n (C (p ∨ q) ∧ I p ∧ ((∇) q)) ((∇) p) ((I p) ∧ q) a
nm_ten p q v = vassume (((*∇) (q)) ≽ ((*∇) p)) $ 
                 cassume ((q*→) ≽ (p*→)) 
                  (reprotect_b v)

