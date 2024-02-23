{-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
    DataKinds, RankNTypes, FlexibleInstances, FlexibleContexts, TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE InstanceSigs #-}
-- {-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Flame.TCB.NMIFC
  where

import Data.Proxy (Proxy(..))
import Data.Constraint
import Data.Constraint.Unsafe
import Data.Reflection

import Flame.Principals
import Flame.TCB.Assume
import Flame.TCB.IFC (Labeled(..), Lbl(..))
import qualified Flame.TCB.IFC as F (FLA(..)) 

class (Monad e, Labeled n) => NMFLA (m :: KPrin -> (* -> *) -> (KPrin -> * -> *) -> KPrin -> KPrin -> * -> *) e n where
  lift :: n l a -> m β e n pc l a

  apply  :: (pc ⊑ pc', pc ⊑ pc'', β' ⊑ β, β'' ⊑ β) =>
            m β e n pc l a -> (n l a -> m β' e n pc' l' b) -> m β'' e n pc'' l' b

  ebind  :: (l ⊑ l', l ⊑ pc', l ⊑ β) => n l a -> (a -> m β e n pc' l' b) -> m β' e n pc l' b

  use :: forall l l' pc pc' pc'' β β' β'' a b. (l ⊑ l', (pc ⊔ l) ⊑ pc', pc ⊑ pc'', l ⊑ β', β' ⊑ β, β'' ⊑ β) =>
         m β e n pc l a -> (a -> m β' e n pc' l' b) -> m β'' e n pc'' l' b
  use x f = apply x $ \x' -> (ebind x' f :: m β' e n pc' l' b)

  protect :: a -> m β e n pc l a
  protect = lift . label

  unsafeProtect :: e (n l a) -> m β e n pc l a

  runFLA :: m β e n pc l a -> e (n l a)

  iassume :: (pc ⊑ ((I q) ∧ Δ p), β ⊑ Δ p) =>
              (I p :≽ I q) -> ((I p ≽ I q) => m β e n pc l a) -> m β e n pc l a
  iassume = unsafeAssume

  vassume :: (pc ⊑ ((∇) q ∧ (Δ ((∇) p))), β ⊑ (Δ ((∇) p))) =>
              ((∇) p :≽ (∇) q) -> (((∇) p ≽ (∇) q) => m β e n pc l a) -> m β e n pc l a
  vassume = unsafeAssume

  cassume :: (pc ≽ (∇) q, (∇) p ≽ (∇) q, β ≽ ((∇) q)) => 
              (C p :≽ C q) -> ((C p ≽ C q) => m β e n pc l a) -> m β e n pc l a
  cassume = unsafeAssume

  eassume :: (pc ≽ (∇) (Δ q), (∇) (Δ p) ≽ (∇) (Δ q), β ≽ ((∇) (Δ p))) => 
              (Δ p :≽ Δ q) -> ((Δ p ≽ Δ q) => m β e n pc l a) -> m β e n pc l a
  eassume = unsafeAssume

  reprotect :: forall l l' pc pc' β β' a. (l ⊑ l', pc ⊑ pc', l ⊑ β, β' ⊑ β) => m β e n pc l a -> m β' e n pc' l' a 
  reprotect x = use x (protect :: a -> m β e n SU l' a)

  --ffmap :: (l ⊑ l', (pc ⊔ l) ⊑ pc', (pc ⊔ l) ⊑ β', β' ⊑ β) => (a -> b) -> m n β pc l a -> m n β' pc' l' b
  --ffmap f x = use x (\y -> protect (f y))

  --fjoin  :: (l ⊑ l', (pc ⊔ l) ⊑ pc', (pc ⊔ l) ⊑ β', β' ⊑ β) => m n β pc l (m n β' pc' l' a) -> m n β' pc' l' a
  --fjoin x = use x id
  --
  --{- XXX: The below operations will become unecessary with a GLB solver -}
  --liftx :: SPrin pc -> n l a -> m n β pc l a
  --liftx pc = lift
  --
  --
  --reprotectx :: (l ⊑ l', pc ⊑ pc', β' ⊑ β) => SPrin pc' -> SPrin l' -> m n β pc l a -> m n β' pc' l' a
  --reprotectx pc' l' = reprotect

{- A transformer for effectful labeled computations -}
data NMCtlT (β::KPrin) e (n :: KPrin -> * -> *) (pc :: KPrin) (l :: KPrin) a where
  UnsafeNMIFC :: { runNMIFC :: e (n l a) } -> NMCtlT β e n pc l a

type NMIFC e β pc l a = NMCtlT β e Lbl pc l a

nmifc_lift :: Monad e => Lbl l a -> NMIFC e β pc l a
nmifc_lift  x = UnsafeNMIFC $ Prelude.return x


nmifc_ebind :: (Monad e, l ⊑ l', l ⊑ pc', l ⊑ β) => Lbl l a -> (a -> NMIFC e β pc' l' b) -> NMIFC e β' pc l' b
nmifc_ebind x f = UnsafeNMIFC $ runNMIFC $ f $ unsafeRunLbl x

            
nmifc_apply :: (Monad e, pc ⊑ pc', pc ⊑ pc'', β' ⊑ β, β'' ⊑ β) =>
               NMIFC e β pc l a -> (Lbl l a -> NMIFC e β' pc' l' b) -> NMIFC e β'' pc'' l' b
nmifc_apply x f = UnsafeNMIFC $ do a <- runNMIFC x
                                   runNMIFC $ f a

instance Monad e => NMFLA NMCtlT e Lbl where
  lift    = nmifc_lift 
  ebind   = nmifc_ebind
  apply   = nmifc_apply
  unsafeProtect = UnsafeNMIFC
  runFLA  = runNMIFC

instance NMFLA NMCtlT e Lbl => F.FLA (NMCtlT SU) e Lbl where
  lift    = nmifc_lift 
  ebind   = nmifc_ebind
  apply   = nmifc_apply
  unsafeProtect = UnsafeNMIFC
  runFLA  = runNMIFC
