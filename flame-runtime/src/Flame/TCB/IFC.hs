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
{-# OPTIONS_GHC -fplugin Flame.Solver -fobject-code #-}

module Flame.TCB.IFC where

import Data.Proxy (Proxy(..))
import Data.Constraint
import Data.Constraint.Unsafe
import Data.Reflection

import Flame.Principals
import Flame.TCB.Assume

{- An indexed monad for information flow on pure computation -}
class Labeled (n :: KPrin -> * -> *) where
  label     :: a -> n l a
  unlabel :: (l ⊑ l') => n l a -> (a -> n l' b) -> n l' b
  unsafeUnlabel :: n l a -> a
  
  relabel :: (l ⊑ l') => n l a -> n l' a
  relabel a = unlabel a label

{- Information flow control based on FLAM acts-for constraints -}
class (Monad e, Labeled n) => IFC (m :: (* -> *) -> (KPrin -> * -> *) -> KPrin -> KPrin -> * -> *) e n where
  lift   :: (pc ⊑ l) => n l a -> m e n pc l a

  apply  :: (pc ⊑ pc', pc ⊑ pc'') => m e n pc l a -> (n l a -> m e n pc' l' b) -> m e n pc'' l' b

  bind  :: (l ⊑ l', l ⊑ pc) => n l a -> (a -> m e n pc l' b) -> m e n pc' l' b

  unsafeProtect :: e (n l a) -> m e n pc l a

  runIFC :: m e n pc l a -> e (n l a)

  protect :: (pc ⊑ l) => a -> m e n pc l a
  protect = lift . label

  use :: forall l l' pc pc' pc'' a b. (l ⊑ l', pc ⊑ pc', l ⊑ pc', pc ⊑ pc'') =>
         m e n pc l a -> (a -> m e n pc' l' b) -> m e n pc'' l' b
  use x f = apply x $ \x' -> (bind x' f :: m e n pc' l' b)
 
  reprotect :: forall l l' pc pc' a. (l ⊑ l', pc ⊑ pc', (pc ⊔ l) ⊑ l') => m e n pc l a -> m e n pc' l' a 
  reprotect x = use x (protect :: a -> m e n (pc ⊔ l) l' a)

  ffmap :: forall l l' pc pc' a b. (l ⊑ l', pc ⊑ pc', l ⊑ pc', pc' ⊑ l') => (a -> b) -> m e n pc l a -> m e n pc' l' b
  ffmap f x = use x (\x' -> protect (f x') :: m e n (pc ⊔ l) l' b)

  fjoin  :: forall l l' pc pc' a. (l ⊑ l',  pc ⊑ pc', l ⊑ pc') => m e n pc l (m e n pc' l' a) -> m e n pc' l' a
  fjoin x = use x id

{- Flow-limited authorization for IFC types -}
class IFC m e n => FLA m e n where
  weak_assume :: (pc ≽ ((I q) ∧ (∇) q), (∇) p ≽ (∇) q) =>
              (p :≽ q) -> ((p ≽ q) => m e n pc l a) -> m e n pc l a
  weak_assume = unsafeAssume
  assume :: (pc ≽ ((I q) ∧ (∇) q)) =>
              (p :≽ q) -> ((p ≽ q, (∇) p ≽ (∇) q) => m e n pc l a) -> m e n pc l a
  assume (Del p q) f = unsafeAssume ((*∇) p ≽ (*∇) q) $ unsafeAssume (p ≽ q) f


{- Nonmalleable information flow control -}
class IFC m e n => NMIF m e n where
  declassify :: (((C pc) ⊓ (C l')) ⊑ (C l)
                 , (C pc) ⊑ (C l')
                 , (C l') ⊑ ((C l) ⊔ (Δ (I l' ⊔ I pc)))
                 , (I l') === (I l)) =>
             m e n pc l' a -> m e n pc l a 
  declassify x = unsafeProtect $ do
    x' <- runIFC x 
    return $ label (unsafeUnlabel x')
  endorse    :: ( ((I pc) ⊓ (I l')) ⊑ (I l)
                , (I pc) ⊑ (I l')
                , (I l') ⊑ ((I l) ⊔ ((∇) (C l' ⊔ C pc)))
                , (C l') === (C l)
                ) =>
             m e n pc l' a -> m e n pc l a 
  endorse x = unsafeProtect $ do
    x' <- runIFC x 
    return $ label (unsafeUnlabel x')

{- A type for pure labeled computations -}
-- both the constructor and destructor must be private:
--   since either will unlabel a value
--   (the constructor enables pattern matching)
data Lbl (l::KPrin) a where
  UnsafeMkLbl :: { unsafeRunLbl :: a } -> Lbl l a

lbl_label :: a -> Lbl l a
lbl_label = UnsafeMkLbl

lbl_unlabel :: (l ⊑ l') => Lbl l a -> (a -> Lbl l' b) -> Lbl l' b    
lbl_unlabel x f = f (unsafeRunLbl x)

{- A Labeled instance for Lbl -}
instance Labeled Lbl where
  label = lbl_label
  unlabel = lbl_unlabel
  unsafeUnlabel = unsafeRunLbl

{- A transformer for effectful labeled computations -}
data FLACT e (n :: KPrin -> * -> *) (pc :: KPrin) (l :: KPrin) a where
  UnsafeFLAC :: { runFLAC :: e (n l a) } -> FLACT e n pc l a

{- FLAC computations -}
type FLAC e pc l a = FLACT e Lbl pc l a

flac_lift :: Monad e => Lbl l a -> FLAC e pc l a
flac_lift  x = UnsafeFLAC $ Prelude.return x

flac_bind :: (Monad e, l ⊑ l', l ⊑ pc') => Lbl l a -> (a -> FLAC e pc' l' b) -> FLAC e pc l' b
flac_bind x f = UnsafeFLAC $ runFLAC $ f $ unsafeRunLbl x

flac_apply :: (Monad e, pc ⊑ pc', pc ⊑ pc'') => FLAC e pc l a -> (Lbl l a -> FLAC e pc' l' b) -> FLAC e pc'' l' b
flac_apply x f = UnsafeFLAC $ do
                   a <- runFLAC x
                   runFLAC $ f a

instance Monad e => IFC FLACT e Lbl where
  lift  = flac_lift 
  apply = flac_apply
  bind  = flac_bind
  unsafeProtect = UnsafeFLAC
  runIFC  = runFLAC

instance Monad e => FLA FLACT e Lbl where {}

{- A transformer for effectful labeled computations -}
data NMT e (n :: KPrin -> * -> *) (pc :: KPrin) (l :: KPrin) a where
  UnsafeNM :: { runNM :: e (n l a) } -> NMT e n pc l a

type NM e pc l a = NMT e Lbl pc l a

nmif_lift :: Monad e => Lbl l a -> NM e pc l a
nmif_lift  x = UnsafeNM $ Prelude.return x

nmif_bind :: (Monad e, l ⊑ l', l ⊑ pc') => Lbl l a -> (a -> NM e pc' l' b) -> NM e pc l' b
nmif_bind x f = UnsafeNM $ runNM $ f $ unsafeRunLbl x

nmif_apply :: (Monad e, pc ⊑ pc', pc ⊑ pc'') => NM e pc l a -> (Lbl l a -> NM e pc' l' b) -> NM e pc'' l' b
nmif_apply x f = UnsafeNM $ do
                   a <- runNM x
                   runNM $ f a

instance Monad e => IFC NMT e Lbl where
  lift    = nmif_lift 
  bind   = nmif_bind
  apply   = nmif_apply
  unsafeProtect = UnsafeNM
  runIFC  = runNM

instance Monad e => NMIF NMT e Lbl where {}