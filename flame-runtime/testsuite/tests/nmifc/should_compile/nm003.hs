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

three :: FLA m e n => SPrin p -> SPrin q
       -> m e n ((∇) q) (C (p ∧ q) ∧ (I q)) a
       -> m e n ((∇) q) (C p ∧ I q)  a
three p q v = assume ((*∇) (p) ≽ (*∇) (q)) $
                assume ((p*→) ≽ (q*→)) (reprotect v)

{- #3 -}
nm_three :: (BFLA c m e n, p ~ N p', q ~ N q') => SPrin p -> SPrin q
       -> c m e n (Δ ((∇) p) ∧ I q) ((∇) q) (C (p ∧ q) ∧ I q) a
       -> c m e n (Δ ((∇) p) ∧ I q) ((∇) q) (C p ∧ I q) a
nm_three p q v = vassume ((*∇) (p) ≽ ((*∇) (q))) $
                  cassume ((p*→) ≽ (q*→)) (reprotect_b v)

