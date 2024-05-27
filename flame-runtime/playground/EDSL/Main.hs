{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Main where

import Data.Int
import Data.Functor.Identity
import Text.PrettyPrint.Mainland

import Control.Monad.Operational.Higher (singleInj, reexpress, (:+:), Program, Param2)

import Language.Embedded.Expression
import Language.Embedded.Imperative ()
import Language.Embedded.Backend.C
import Language.Embedded.CExp
import Language.Embedded.Signature
import Language.C.Monad 
import Language.Embedded.Imperative.CMD hiding (stdin, stdout)

import Flame.EDSL.Do
import Flame.EDSL.IFC
import Flame.EDSL.Frontend
import Flame.Principals
import Flame.Runtime.Principals

class    (Eq a, Ord a, Show a, CType a) => Type a
instance (Eq a, Ord a, Show a, CType a) => Type a

data HighExp a where
  HUnit :: HighExp ()
  HVar  :: Type a => VarId -> HighExp a
  HLit  :: Type a => a -> HighExp a

  HAdd  :: (Num a, Type a) => HighExp a -> HighExp a -> HighExp a
  HMul  :: (Num a, Type a) => HighExp a -> HighExp a -> HighExp a

  HNot  :: HighExp Bool -> HighExp Bool
  HEq   :: Type a => HighExp a -> HighExp a -> HighExp Bool

  --HInjL  :: (Type a, Type b) => HighExp a -> HighExp (Either a b)
  --HInjR  :: (Type a, Type b) => HighExp b -> HighExp (Either a b)
  --HCase  :: (Type a, Type b, Type c) => HighExp (Either a b)
  --                                      -> (HighExp a -> HighExp c)
  --                                      -> (HighExp b -> HighExp c)
  --                                      -> HighExp c

instance (Num a, Type a) => Num (HighExp a) where
  fromInteger = HLit . fromInteger
  (+) = HAdd
  (*) = HMul

instance FreeExp HighExp
  where
    type FreePred HighExp = Type
    constExp = HLit
    varExp = HVar

type CMD
    =   RefCMD      -- Mutable references
    :+: ControlCMD  -- Control structures
    :+: FileCMD     -- Input/output

transHighExp :: forall exp pc l a. HighExp a -> Program CMD (Param2 CExp CType) (CExp a)
transHighExp (HVar v)    = return (varExp v)
transHighExp (HLit a)    = return (constExp a)
transHighExp (HAdd a b)  = (+)   <$> transHighExp a <*> transHighExp b
transHighExp (HMul a b)  = (*)   <$> transHighExp a <*> transHighExp b
transHighExp (HNot a)    = not_  <$> transHighExp a
transHighExp (HEq a b)   = (#==) <$> transHighExp a <*> transHighExp b

instance HasBackend HighExp CExp CMD CType where
  translateExp e = do
    cexp <- transHighExp e
    return cexp

doMultiplyInputs :: LABProgram HighExp CMD CType KBot KBot () 
doMultiplyInputs = [flame| do
                     printf "Please enter two numbers\n"
                     printf (" > "); m :: HighExp Int32 <- fget stdin
                     printf "m: %d\n" m
                     printf " > "; n :: HighExp Int32 <- fget stdin
                     printf "n: %d\n" n
                     printf "m*n = %d\n" $ (m*n)
                   |]

main = do
  putDoc $ case (compileLAB "main" doMultiplyInputs) of
              [(s,d)] -> d
