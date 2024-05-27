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

assertBots :: (C ('KConf 'KBot) ≽ C 'KBot, I 'KBot ≽ I ('KConf 'KBot)) => ()
assertBots = ()

eqTBotConf = assertBots
