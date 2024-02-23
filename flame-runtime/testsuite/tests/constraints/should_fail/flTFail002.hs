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

flTConfConjL :: SPrin p ->  SPrin q -> ()
flTConfConjL p q = assertFlowsTo ((p *∧ q)*→) (p*→)
