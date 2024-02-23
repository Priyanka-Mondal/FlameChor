{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

----------------------------------------------------------------------------
---- Based on Language.Haskell.IndexedDo by Fumiaki Kinoshita
----------------------------------------------------------------------------
module Flame.EDSL.Do (flame) where

import Language.Haskell.Meta
import Language.Haskell.TH
import Language.Haskell.TH.Quote

import Flame.EDSL.IFC

flame :: QuasiQuoter
flame = QuasiQuoter { quoteExp = \str -> case parseExp str of
        Right (DoE ss) -> return (go ss)
        Right _ -> fail "Expecting do notation"
        Left err -> fail (show err)
        , quotePat = undefined
        , quoteType = \str -> case parseType str of
        Right t -> return t
        Left err -> fail (show err)
        , quoteDec = undefined
        } where
    go [NoBindS e] = e
    go (BindS p e : ss) = VarE 'use `AppE` e `AppE` LamE [p] (go ss)
    go (NoBindS e : ss) = VarE 'apply `AppE` e `AppE` LamE [WildP] (go ss)
    go (LetS ds : ss) = LetE ds (go ss)