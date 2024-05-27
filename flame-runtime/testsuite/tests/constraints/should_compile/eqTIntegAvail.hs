
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


eqTIntegAvail :: SPrin p -> ()
eqTIntegAvail p = assertEq ((p*←)*|^) SBot
--eqTConfIntegBasis :: SPrin p -> ()
--eqTConfIntegBasis p = assertEq ((p*←) *∧ (p*→)) p
