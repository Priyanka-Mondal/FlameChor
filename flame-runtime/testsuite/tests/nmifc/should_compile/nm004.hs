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

four :: FLA m e n => SPrin p -> SPrin q
       -> m e n ((∇) p) (C (p ∧ q) ∧ (I q)) a
       -> m e n ((∇) p) q  a
four p q v = assume ((*∇) (q) ≽ (*∇) (p)) $
                assume ((q*→) ≽ (p*→)) (reprotect v)

{- #4 (allowed) google doc says this is insecure 
 -   only types if p and q are primitive..
 - -}
nm_four :: (BFLA c m e n, q ⊑ Δ q, p ~ N p', q ~ N q') => SPrin p -> SPrin q
       -> c m e n (Δ ((∇) q) ∧ I q) ((∇) p) (C (p ∧ q) ∧ I q) a
       -> c m e n (Δ ((∇) q) ∧ I q) ((∇) p) q a
nm_four p q v = vassume ((*∇) (q) ≽ ((*∇) (p))) $
                  cassume ((q*→) ≽ (p*→)) (reprotect_b v)

