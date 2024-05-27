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

seven :: FLA m e n => SPrin p -> SPrin q -> m e n (I p) (C p ∧ I q) a -> m e n (I p) (p ∧ I q) a
seven p q v = assume (q ≽ (p*←)) (reprotect v)
{- #7 this is similar to badreceive -}
{- Fails (as desired)
nm_seven :: (BFLA c m e n) =>
                 SPrin p
                 -> SPrin q
                 -> m e n (Δ q) (I p) (C p ∧ I q) a
                 -> m e n (Δ q) (I p) (p ∧ I q) a
nm_seven p q v = iassume ((q*←) ≽ (p*←)) (reprotect_b v)
-}
