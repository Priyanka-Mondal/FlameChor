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

{- #11 -}
eleven :: (FLA m e n, r ≽ q) =>
          SPrin p
          -> SPrin q
          -> SPrin r
          -> m e n ((∇) p) (p ∧ (I q)) a
          -> m e n ((∇) p) ((I p) ∧ (I q) ∧ (C r)) a
eleven p q r v = assume ((*∇) (q) ≽ (*∇) (p)) $ assume ((q*→) ≽ (p*→)) (reprotect v)

--Broken by cassume integrity constraint                                                                 
nm_eleven :: (BFLA c m e n, r ≽ q, p ~ N p', q ~ N q', r ~ N r') =>
           SPrin p
           -> SPrin q
           -> SPrin r
           -> c m e n (C q ∧ I p ∧ I q) ((∇) p) (p ∧ (I q)) a
           -> c m e n (C q ∧ I p ∧ I q) ((∇) p) ((I p) ∧ (I q) ∧ (C r)) a
nm_eleven p q r v = iassume ((((*∇) (q))*←) ≽ (((*∇) (p))*←)) $
                 cassume ((q*→) ≽ (p*→)) (reprotect_b v)

