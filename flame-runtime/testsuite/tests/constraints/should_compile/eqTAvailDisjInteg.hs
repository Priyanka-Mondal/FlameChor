
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


eqTAvailDisjInteg :: SPrin p -> SPrin q -> ()
eqTAvailDisjInteg p q = assertEq ((p*|^) *∨ (q*←)) SBot
