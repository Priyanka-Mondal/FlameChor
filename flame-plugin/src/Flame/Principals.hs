{-# LANGUAGE GADTs, PolyKinds, DataKinds, RankNTypes #-}
{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Flame.Principals
       ( KPrin (..)
       , SPrin (..)
       , C, I, type (^->), type (^→), type (^<-), type (^←)
       , N, Public, Secret, Trusted, Untrusted, PT, SU 
       , DPrin (st, dyn), Ex(..) 
       , withPrin, promote
       , type (/\), type (∧), type (\/), type (∨) 
       , type (⊔), type (⊓)
       , type (≽), type (>=), type (⊑), type (<:), type (===)
       , type (∇), Voice, Δ, Eye, (∇), δ 
       , (⊤), top, (⊥), bot
       , public, trusted, publicTrusted, secret, untrusted, secretUntrusted
       , (^->), (^→), (^<-), (^←)
       , (/\), (∧), (\/), (∨), (⊔), (⊓)
       , (*->), (*→), (*<-), (*←), (*/\), (*∧), (*\/), (*∨), (*⊔), (*⊓), (*∇)  
       , (<=>) -- XXX TODO: should not export to non-TCB code.
       )
where

import Data.Constraint hiding (top)
import GHC.TypeLits
import Data.Proxy (Proxy(..))
import Data.Type.Bool
import Data.Data
import Data.Text  (pack, unpack)

import Flame.Runtime.Principals

{-| The principal kind. Type-level FLAM principals |-}
data KPrin =
  KTop
  | KBot
  | KName  Symbol 
  | KConj  KPrin KPrin 
  | KDisj  KPrin KPrin
  | KConf  KPrin
  | KInteg KPrin
  | KVoice KPrin
  | KEye   KPrin

{-| 
Singleton GADT for KPrin. This GADT associates a KPrin (which is an
uninstantiable kind) with a single runtime value, providing a link
between runtime principals and type-level principals.  NB: we employ
an explicit singleton pattern here b/c the singletons package cannot
promote strings to symbols.
|-}
data SPrin :: KPrin -> * where
  STop   :: SPrin KTop
  SBot   :: SPrin KBot
  SName  :: forall (n :: Symbol). { sym :: Proxy n } -> SPrin (KName n)
  SConj  :: !(SPrin p) -> !(SPrin q) -> SPrin (KConj p q)
  SDisj  :: !(SPrin p) -> !(SPrin q) -> SPrin (KDisj p q)
  SConf  :: !(SPrin p) -> SPrin (KConf p)
  SInteg :: !(SPrin p) -> SPrin (KInteg p)
  SVoice :: !(SPrin p) -> SPrin (KVoice p)
  SEye   :: !(SPrin p) -> SPrin (KEye   p)

deriving instance Show (SPrin p)
deriving instance Eq (SPrin p)

{- Some notation help -}
type C p      = KConf p
type (^→) p  = KConf p
type (^->) p  = KConf p
type I p      = KInteg p
type (^←) p  = KInteg p
type (^<-) p  = KInteg p
type Voice p  = KVoice p
type Eye p    = KEye p
type N s      = KName s

type (/\) p q = KConj p q
type p ∧ q  = KConj p q
infixl 7 /\
infixl 7 ∧

type (\/) p q = KDisj p q
type (∨)  p q = KDisj p q
infixl 7 ∨

type (∇) p = Voice p
type (Δ) p = Eye p

-- TODO: convert flow join/meet to type families so that
--       resulting types are more normalized
type (⊔) p q  = (C p ∧ C q) ∧ (I p ∨ I q)
infixl 6 ⊔
type (⊓) p q  = (C p ∨ C q) ∧ (I p ∧ I q)
infixl 6 ⊓

type (⊤) = KTop
type (⊥) = KBot
type Public   = C KBot
type Trusted  = I KTop
type PT       = Public ∧ Trusted 

type Secret = C KTop
type Untrusted  = I KBot
type SU       = Secret ∧ Untrusted

(*->) p   = SConf p
(*→)  p   = SConf p

(*<-) p   = SInteg p
(*←) p   = SInteg p

(*∇)  p = SVoice p

(*/\) p q  = SConj p q
(*∧)  p q  = SConj p q

(*\/) p q  = SDisj p q
(*∨)  p q  = SDisj p q

(*⊔)  p q  = ((p*→) *∧ (q*→)) *∧ ((p*←) *∨ (q*←))
(*⊓)  p q  = ((p*→) *∨ (q*→)) *∧ ((p*←) *∧ (q*←))

public :: SPrin Public
public = SConf SBot
trusted  :: SPrin Trusted
trusted  = SInteg STop
publicTrusted :: SPrin PT
publicTrusted = public *∧ trusted

secret :: SPrin Secret
secret = (SConf STop)
untrusted  :: SPrin Untrusted
untrusted  = (SInteg SBot)
secretUntrusted :: SPrin SU
secretUntrusted = secret *∧ untrusted

{- Existential wrapper -}
data Ex (p :: k -> *) where
  Ex :: p i -> Ex p

{- Promote runtime principals to existentially-wrapped principal types -}
promoteS :: Prin -> Ex SPrin
promoteS p =
  case p of
    Top         ->  Ex STop
    Bot         ->  Ex SBot
    (Name str)  ->  case someSymbolVal (unpack str) of
                      SomeSymbol n -> Ex (SName n)
    (Conj p q)  ->  case promoteS p of
                      Ex p' -> case promoteS q of
                                 Ex q' -> Ex (SConj p' q')
    (Disj p q)  ->  case promoteS p of
                      Ex p' -> case promoteS q of
                                 Ex q' -> Ex (SDisj p' q')
    (Conf p)    ->  case promoteS p of Ex p' -> Ex (SConf p')
    (Integ p)   ->  case promoteS p of Ex p' -> Ex (SInteg p')

{- Bind runtime principal to type -}
withPrin :: Prin -> (forall p . DPrin p -> a) -> a
withPrin p f = case promote p of
                 Ex p' -> f p'

promote :: Prin -> Ex DPrin
promote p = case promoteS p of
              Ex p' -> Ex (p <=> p')


{-| DPrin p is a record associating a dynamic principal with a
singleton principal. This construction is necessary since not all
principal names may be known at compile-time, yet we still 
want to construct a type-level representation for runtime principals.

Restricting <=> and UnsafeAssoc to trusted code ensures only withPrin
can associate runtime principals wth singleton principal types.
|-}
data DPrin p = UnsafeAssoc { dyn :: Prin, st :: !(SPrin p) } 
dynamic = dyn
static = st 
(<=>) :: Prin -> SPrin p -> DPrin p
p <=> sp = UnsafeAssoc p sp

{-| Notation helpers for DPrin values |-} 
(⊤) :: DPrin (⊤)
(⊤) = Top <=> STop
top = (⊤)

(⊥) :: DPrin (⊥)
(⊥) = Bot <=> SBot
bot = (⊥)

(^→) :: DPrin p  -> DPrin (C p)
(^→) p  = Conf (dyn p) <=> SConf (st p)
(^->) = (^→)

(^←) :: DPrin p  -> DPrin (I p)
(^←) p = Integ (dyn p) <=> SInteg (st p)
(^<-) = (^←)

(∧) :: DPrin p -> DPrin q -> DPrin (p ∧ q) 
(∧) p q = Conj (dyn p) (dyn q) <=> SConj (st p) (st q)
(/\) = (∧)

(∨) :: DPrin p -> DPrin q -> DPrin (p ∨ q) 
(∨)  p q  = Disj (dyn p) (dyn q) <=> SDisj (st p) (st q)
(\/) = (∨)

(⊔) :: DPrin p -> DPrin q -> DPrin (p ⊔ q) 
(⊔)  p q  = (Conj (Conf (Conj (dyn p) (dyn q)))
             (Integ (Disj (dyn p) (dyn q)))) <=> ((st p) *⊔ (st q))
join = (⊔)

(⊓) :: DPrin p -> DPrin q -> DPrin (p ⊓ q) 
(⊓) p q  = (Conj (Conf (Disj (dyn p) (dyn q)))
            (Integ (Conj (dyn p) (dyn q)))) <=> ((st p) *⊓ (st q))
meet = (⊓)

(∇) :: DPrin p -> DPrin ((∇) p)
(∇) p = voiceOf (dyn p) <=> SVoice (st p)
        
δ :: DPrin p -> DPrin (Δ p)
δ p = eyeOf (dyn p) <=> SEye (st p)

{-| Actsfor constraints. This type family is closed: only the Flame solver is capable of resolving these constraints.  |-}
type family (≽) (p :: KPrin) (q :: KPrin) :: Constraint where
infixl 4 ≽

{- Type synonyms for acts for constraints. As in FLAM, the safe
information flow relation is defined in terms of the acts-for
relation. -}
type (>=) (p :: KPrin) (q :: KPrin) = (p ≽ q) 
infixl 4 >=
type (⊑) (p :: KPrin) (q :: KPrin) = (C q ≽ C p , I p ≽ I q) 
infixl 4 ⊑
type (<:) (p :: KPrin) (q :: KPrin) = (p ⊑ q)
infixl 4 <:
type (===) (p :: KPrin) (q :: KPrin) = (p ≽ q, q ≽ p)
infixl 4 ===
