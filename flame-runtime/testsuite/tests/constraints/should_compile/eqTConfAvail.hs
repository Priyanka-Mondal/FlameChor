
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


eqTConfAvail :: SPrin p -> ()
eqTConfAvail p = assertEq ((p*→)*|^) SBot
eqTConfIntegAvailBasis :: SPrin p -> ()
eqTConfIntegAvailBasis p = assertEq ((p*←) *∧ ((p*→) *∧ (p*|^))) p
