
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


eqTConjAvail :: SPrin p -> SPrin q -> ()
eqTConjAvail p q = assertEq ((p *∧ q)*|^) ((p*|^) *∧ (q*|^))