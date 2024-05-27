
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}
module ShouldSucceed where

import Flame.Assert
import Flame.Principals


eqTTrans2 :: (p ≽ q, q ≽ r, r ≽ q, q ≽ p) => SPrin p -> SPrin q -> SPrin r -> ()
eqTTrans2 p q r = assertEq p r
