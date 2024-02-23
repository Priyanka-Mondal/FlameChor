{-# LANGUAGE GADTs, PolyKinds, KindSignatures, MultiParamTypeClasses,
    DataKinds, RankNTypes, FlexibleInstances, FlexibleContexts, TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin Flame.Solver -fobject-code #-}

module Flame.Runtime.Sealed
 --      (Sealed, seal, withSealed, sealWith)
where

import Flame.Principals
import Flame.Runtime.Principals
import Flame.TCB.IFC
import Flame.TCB.Assume

import qualified Data.Map as M
 
data Sealed n a where
  Seal :: Labeled n => DPrin l -> n l a -> Sealed n a

seal :: Labeled n => DPrin l -> n l a -> Sealed n a
seal = Seal

unseal :: Labeled n => Sealed n a -> (forall l . DPrin l -> n l a -> b) -> b
unseal s f = case s of
               Seal l lv -> f l lv

unsealWith :: Labeled n => DPrin l -> Sealed n a -> (n l a -> b) -> Maybe b
unsealWith l s f =
  case s of
    Seal l' lv -> case l `eq` l' of
                    Just Equiv -> Just $ f (relabel lv)
                    _ -> Nothing

data SealedIFC m e n a where
  SealIFC :: (IFC m e n, pc ⊑ l) => DPrin pc -> DPrin l -> m e n pc l a -> SealedIFC m e n a

sealIFC :: (IFC m e n, pc ⊑ l) => DPrin pc -> DPrin l -> m e n pc l a -> SealedIFC m e n a
sealIFC = SealIFC

unsealIFC :: IFC m e n =>
             SealedIFC m e n a
          -> (forall pc l . DPrin pc -> DPrin l -> m e n pc l a -> b)
          -> b
unsealIFC s f = case s of
                  SealIFC pc l lv -> f pc l lv

unsealIFCWith :: IFC m e n =>
                 DPrin pc
              -> DPrin l
              -> SealedIFC m e n a
              -> (m e n pc l a -> b)
              -> Maybe b
unsealIFCWith pc l s f =
  case s of
    SealIFC pc' l' lv ->
      case l `eq` l' of
        Just Equiv ->
          case pc `eq` pc' of
            Just Equiv -> Just $ f (reprotect lv)
            _ -> Nothing
        _ -> Nothing

data SealedType (k :: KPrin -> * -> *) a where
  SealType :: DPrin l -> k l a -> SealedType k a

sealType :: DPrin l -> k l a -> SealedType k a
sealType = SealType

unsealType :: SealedType k a -> (forall l. DPrin l -> k l a -> b) -> b
unsealType s f = case s of
                   SealType l lv -> f l lv

unsealTypeWith :: DPrin l
               -> SealedType k a
               -> (forall l'. (l === l') => DPrin l' -> k l' a -> b)
               -> Maybe b
unsealTypeWith l s f =
  case s of
    SealType l' lv -> case l `eq` l' of
                        Just Equiv -> Just $ f l' lv 
                        _ -> Nothing
