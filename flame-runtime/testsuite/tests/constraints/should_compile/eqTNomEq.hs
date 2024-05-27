{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}
module ShouldFail where

import Flame.Assert
import Flame.Principals

eqTNomEq :: (p ~ q) => SPrin p -> SPrin q -> ()
eqTNomEq p q = assertEq p q
