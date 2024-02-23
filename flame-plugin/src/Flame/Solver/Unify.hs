{-|
Copyright  :  (C) 2015-2016, University of Twente
License    :  BSD2 (see the file LICENSE)
Maintainer :  Christiaan Baaij <christiaan.baaij@gmail.com>
-}

{-# LANGUAGE CPP                        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash                  #-}
{-# LANGUAGE RecordWildCards            #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}
#if __GLASGOW_HASKELL__ < 801
#define nonDetCmpType cmpType
#endif

module Flame.Solver.Unify
  ( -- * 'Nat' expressions \<-\> 'Norm' terms
    -- * Free variables in 'Norm' terms
    fvNorm
  , fvJNorm
  )
where

-- External
import Data.List     ((\\), intersect, mapAccumL)
import GHC.Types.Unique.Set (UniqSet, unionManyUniqSets, emptyUniqSet, unionUniqSets,
                       unitUniqSet)
import Data.Map.Strict (insert, findWithDefault)

-- GHC API
import GHC.Plugins
-- import Outputable    (Outputable (..), (<+>), ($$), text, pprTrace)
-- import TcType     (isSkolemTyVar)
-- import TcPluginM     (TcPluginM, tcPluginTrace)
-- import TcRnMonad     (Ct, ctEvidence, isGiven)
-- import TcRnTypes     (ctEvPred)
-- import TcTypeNats    (typeNatAddTyCon, typeNatExpTyCon, typeNatMulTyCon,
--                       typeNatSubTyCon)
-- import Type          (EqRel (NomEq), PredTree (EqPred), TyVar, classifyPredType,
--                       coreView, eqType, mkNumLitTy, mkTyConApp, mkTyVarTy,
--                       nonDetCmpType)
-- import TyCoRep       (Type (..), TyLit (..))

-- Internal
import Flame.Solver.Data
import Flame.Solver.Norm
import Flame.Solver.ActsFor

---- | A substitution is essentially a list of (variable, 'Norm') pairs,
---- but we keep the original 'Ct' that lead to the substitution being
---- made, for use when turning the substitution back into constraints.
--type CoreUnify = UnifyItem TyVar Type
--
---- | Result of comparing two 'Norm' terms, returning a potential substitution
---- list under which the two terms are equal.

-- | Given two 'Norm's @u@ and @v@, when their free variables ('fvNorm') are the
-- same, then we 'Win' if @u@ and @v@ are equal, and 'Lose' otherwise.
--
{- | Collect the free variables of a normalized principal -}
fvNorm :: CoreNorm -> UniqSet TyVar
fvNorm (N conf integ) = fvJNorm conf `unionUniqSets` fvJNorm integ

-- | Find the 'TyVar' in a 'CoreJNorm'
fvJNorm :: CoreJNorm -> UniqSet TyVar
fvJNorm = unionManyUniqSets . map fvMNorm . unJ

fvMNorm :: CoreMNorm -> UniqSet TyVar
fvMNorm = unionManyUniqSets . map fvBase . unM

fvBase :: CoreBase -> UniqSet TyVar
fvBase (P _) = emptyUniqSet
fvBase (U _) = emptyUniqSet
fvBase B     = emptyUniqSet
fvBase T     = emptyUniqSet
fvBase (V v)        = unitUniqSet v
fvBase (VarVoice v) = unitUniqSet v
fvBase (VarEye v)   = unitUniqSet v
fvBase (UVoice _)   = emptyUniqSet
fvBase (UEye _)     = emptyUniqSet