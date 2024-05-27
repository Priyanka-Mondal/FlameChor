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

eqTSym :: (l === l') => SPrin l -> SPrin l' -> ()
eqTSym l l' = assertEq l l'

eqTTrans :: (p ≽ q, q ≽ r) => SPrin p -> SPrin q -> SPrin r -> ()
eqTTrans p q r = assertActsFor p r

eqTTrans2 :: (p ≽ q, q ≽ r, r ≽ q, q ≽ p) => SPrin p -> SPrin q -> SPrin r -> ()
eqTTrans2 p q r = assertEq p r

eqTTrans3 :: (p ⊑ q, q ⊑ r) => SPrin p -> SPrin q -> SPrin r -> ()
eqTTrans3 p q r = assertFlowsTo p r

eqTTrans4 :: (p === q, q === r) => SPrin p -> SPrin q -> SPrin r -> ()
eqTTrans4 p q r = assertEq p r

eqTConjComm :: SPrin p -> SPrin q -> ()
eqTConjComm p q = assertEq (p *∧ q) (q *∧ p) 

eqTDisjComm :: SPrin p -> SPrin q -> ()
eqTDisjComm p q = assertEq (p *∨ q) (q *∨ p) 

eqTConjAssoc :: SPrin p -> SPrin q -> SPrin r -> ()
eqTConjAssoc p q r = assertEq ((p *∧ q) *∧ r) (p *∧ (q *∧ r))

eqTDisjAssoc :: SPrin p -> SPrin q -> SPrin r -> ()
eqTDisjAssoc p q r = assertEq ((p *∨ q) *∨ r) (p *∨ (q *∨ r))

eqTDisjAbsorb :: SPrin p -> SPrin q -> ()
eqTDisjAbsorb p q = assertEq (p *∧ (p *∨ q)) p 
                    
eqTConjAbsorb :: SPrin p -> SPrin q -> ()
eqTConjAbsorb p q = assertEq (p *∨ (p *∧ q)) p 

eqTConjIdemp :: SPrin p -> ()
eqTConjIdemp p = assertEq (p *∧ p) p 

eqTDisjIdemp :: SPrin p -> ()
eqTDisjIdemp p = assertEq (p *∨ p) p 

eqTConjIdent :: SPrin p -> ()
eqTConjIdent p = assertEq (p *∧ SBot) p 
                 
eqTDisjIdent :: SPrin p -> ()
eqTDisjIdent p = assertEq (p *∨ STop) p 

eqTConjTop :: SPrin p -> ()
eqTConjTop p = assertEq (p *∧ STop) STop 
       
eqTDisjBot :: SPrin p -> ()
eqTDisjBot p = assertEq (p *∨ SBot) SBot

eqTConjDistDisj :: SPrin p -> SPrin q -> SPrin r -> ()
eqTConjDistDisj p q r = assertEq (p *∧ (q *∨ r)) ((p *∧ q) *∨ (p *∧ r))

eqTConjConf :: SPrin p -> SPrin q -> ()
eqTConjConf p q = assertEq ((p *∧ q)*→) ((p*→) *∧ (q*→))

eqTConjInteg :: SPrin p -> SPrin q -> ()
eqTConjInteg p q = assertEq ((p *∧ q)*←) ((p*←) *∧ (q*←))

eqTDisjConf :: SPrin p -> SPrin q -> ()
eqTDisjConf p q = assertEq ((p *∨ q)*→) ((p*→) *∨ (q*→))

eqTDisjInteg :: SPrin p -> SPrin q -> ()
eqTDisjInteg p q = assertEq ((p *∨ q)*←) ((p*←) *∨ (q*←))

eqTConfIdemp :: SPrin p -> ()
eqTConfIdemp p = assertEq ((p*→)*→) (p*→)

eqTIntegIdemp :: SPrin p -> ()
eqTIntegIdemp p = assertEq ((p*←)*←) (p*←)

eqTConfInteg :: SPrin p -> ()
eqTConfInteg p = assertEq ((p*→)*←) SBot

eqTIntegConf :: SPrin p -> ()
eqTIntegConf p = assertEq ((p*←)*→) SBot

eqTConfDisjInteg :: SPrin p -> SPrin q -> ()
eqTConfDisjInteg p q = assertEq ((p*→) *∨ (q*←)) SBot

eqTConfIntegBasis :: SPrin p -> ()
eqTConfIntegBasis p = assertEq ((p*←) *∧ (p*→)) p

eqTBotConf :: ()
eqTBotConf = assertEq (SBot*→) SBot

eqTBotInteg :: ()
eqTBotInteg = assertEq (SBot*←) SBot
