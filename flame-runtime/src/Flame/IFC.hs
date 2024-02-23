{-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
    DataKinds, RankNTypes, FlexibleInstances, FlexibleContexts, TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fplugin Flame.Solver -fobject-code #-}

module Flame.IFC
       ( Labeled(label, unlabel,relabel), Lbl
       , IFC(lift, apply, bind, runIFC, protect, use, reprotect, ffmap, fjoin)
       , FLA(..), FLAC, FLACT, NMIF(..), NM, NMT, runFLAC, runNM 
       , (:≽), (:=>=), (:⊑), (:<:)          -- Delegation types
       , Def(..), (≽), (=>=), (⊑), (<:)     -- Delegation constructors
       )
  where

import Flame.TCB.IFC
import Flame.TCB.Assume
