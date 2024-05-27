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
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Flame.EDSL.IFC where

import Data.Proxy (Proxy(..))
import Data.Constraint
import Data.Constraint.Unsafe
import Data.Reflection

import Flame.Principals
-- import Flame.TCB.Assume
import Data.Int
import Data.Functor.Identity
import Text.PrettyPrint.Mainland

{- EDSL imports -}
import Control.Monad.Operational.Higher
import qualified Control.Monad.State as CMS
import Control.Monad.State.Class

import Language.C.Quote.C
import qualified Language.C.Syntax as C

import Language.C.Monad hiding (inModule)
import qualified Control.Monad.Reader as R
import Language.Embedded.Expression
--import Language.Embedded.Imperative hiding (cedecl, RefCMD, Ref)
import Language.Embedded.Backend.C
import Language.Embedded.CExp
import Language.Embedded.Traversal
import Language.Embedded.Imperative.CMD (RefCMD (GetRef), mkParam, mapFunArg, mapFunArgM)

import Flame.Principals

data Label (l::KPrin) a where
  Label   :: a -> Label l a
  Unlabel :: (l ⊑ l') => Label l a -> (a -> Label l' b) -> Label l' b

runLabel :: Label l a -> a
runLabel (Label v) = v
runLabel (Unlabel lv f) = runLabel (f $ runLabel lv)

newtype LABProgram exp instr pred pc l a = LAB { program :: Program instr (Param2 exp pred) a }

lift :: Label l a -> LABProgram exp instr pred pc l a
lift = LAB . return . runLabel

apply :: (pc ⊑ pc', pc ⊑ pc'') => LABProgram exp instr pred pc l a
      -> (Label l a -> LABProgram exp instr pred pc' l' b)
      -> LABProgram exp instr pred pc'' l' b
apply (LAB prog) f = LAB $ do
                             lv <- prog
                             case f (Label lv) of
                               LAB p -> p

bind ::  (l ⊑ l', l ⊑ pc') => Label l a
     -> (a -> LABProgram exp instr pred pc' l' b)
     -> LABProgram exp instr pred pc l' b
bind lv f = LAB $ case f $ runLabel lv of
                    LAB p -> p

class HasBackend exp1 exp2 instr pred where
  translateExp :: exp1 a -> Program instr (Param2 exp2 pred) (exp2 a)

reexpressLAB :: forall instr1 instr2 exp1 exp2 pred pc l a b .
              (Reexpressible instr1 instr2 ()
              , HasBackend exp1 exp2 instr2 pred
              )
             => (forall b . exp1 b -> Program instr2 (Param2 exp2 pred) (exp2 b))
             -> LABProgram exp1 instr1 pred pc l a -> LABProgram exp2 instr2 pred pc l a
reexpressLAB f (LAB p) = LAB $ reexpress @instr1 @instr2 @_ @exp1 @exp2 f p

wrapProc :: MonadC m => String -> m a -> m () 
wrapProc s prog = do
    (_,uvs,params,items) <- inNewFunction $ prog >> addStm [cstm| return 0; |]
    setUsedVars s uvs
    addGlobal [cedecl| int $id:s($params:params){ $items:items }|]

compileLAB :: forall instr exp pred pc l.
              ( HasBackend exp CExp instr pred 
              , Reexpressible instr instr ()
              , Interp instr CGen (Param2 CExp pred)
              , FreeExp exp, RefCMD :<: instr
              )
           => String -> LABProgram exp instr pred pc l () -> [(String,Doc)]
compileLAB s p = prettyCGen . wrapProc s $ (interpret . program) (reexpressLAB @instr @instr @exp @CExp translateExp p)

relabel :: (l ⊑ l') => Label l a -> Label l' a
relabel a = Unlabel a Label 

protect :: (pc ⊑ l) => a -> LABProgram exp instr pred pc l a
protect = lift . Label

use :: forall exp instr pred l l' pc pc' pc'' a b.
       (l ⊑ l', pc ⊑ pc', l ⊑ pc', pc ⊑ pc'')
    => LABProgram exp instr pred pc l a -> (a -> LABProgram exp instr pred pc' l' b) -> LABProgram exp instr pred pc'' l' b
use x f = apply x $ \x' -> (bind x' f :: LABProgram exp instr pred pc' l' b)

(>>>=) :: forall exp instr pred l l' pc pc' pc'' a b.
       (l ⊑ l', pc ⊑ pc', l ⊑ pc', pc ⊑ pc'')
    => LABProgram exp instr pred pc l a -> (a -> LABProgram exp instr pred pc' l' b) -> LABProgram exp instr pred pc'' l' b
x >>>= f = use x f
 
reprotect :: forall exp instr pred l l' pc pc' a.
             (l ⊑ l', pc ⊑ pc', (pc ⊔ l) ⊑ l')
          => LABProgram exp instr pred pc l a -> LABProgram exp instr pred pc' l' a 
reprotect x = use x (protect :: a -> LABProgram exp instr pred (pc ⊔ l) l' a)

ifmap :: forall exp instr pred l l' pc pc' a b.
         (l ⊑ l', pc ⊑ pc', l ⊑ pc', pc' ⊑ l')
      => (a -> b) -> LABProgram exp instr pred pc l a -> LABProgram exp instr pred pc' l' b
ifmap f x = use x (\x' -> protect (f x') :: LABProgram exp instr pred (pc ⊔ l) l' b)

ijoin :: forall exp instr pred l l' pc pc' a. (l ⊑ l',  pc ⊑ pc', l ⊑ pc')
      => LABProgram exp instr pred pc l (LABProgram exp instr pred pc' l' a) -> LABProgram exp instr pred pc' l' a
ijoin x = use x id
