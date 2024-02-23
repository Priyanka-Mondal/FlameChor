{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin Flame.Solver -fobject-code #-}

----------------------------------------------------------------------------
---- Based on Language.Haskell.IndexedDo by Fumiaki Kinoshita
----------------------------------------------------------------------------
module Flame.Do (flame) where

import Language.Haskell.Meta
import Language.Haskell.TH
import Language.Haskell.TH.Quote
import qualified Language.Haskell.Exts.Syntax as Hs
import qualified Language.Haskell.Exts.SrcLoc as Hs
import Language.Haskell.Exts.Extension as Ext
import Language.Haskell.Exts.Parser (ParseMode(..), ParseResult(..), parseExpWithMode)

import Flame.IFC

myDefaultParseMode2 :: ParseMode
myDefaultParseMode2 = ParseMode
  {parseFilename = []
  ,baseLanguage = Haskell2010
  ,extensions = map EnableExtension myDefaultExtensions2
  ,ignoreLinePragmas = False
  ,ignoreLanguagePragmas = False
  ,fixities = Nothing
  ,ignoreFunctionArity = False
  }

myDefaultExtensions2 :: [KnownExtension]
myDefaultExtensions2 = [Ext.PostfixOperators
                      ,Ext.QuasiQuotes
                      ,Ext.UnicodeSyntax
                      ,Ext.PatternSignatures
                      ,Ext.MagicHash
                      ,Ext.ForeignFunctionInterface
                      ,Ext.TemplateHaskell
                      ,Ext.RankNTypes
                      ,Ext.MultiParamTypeClasses
                      ,Ext.RecursiveDo
                      ,Ext.TypeApplications]
  
myParseExp :: String -> Either String Exp
myParseExp = either Left (Right . toExp) . myParseHsExp

myParseHsExp :: String -> Either String (Hs.Exp Hs.SrcSpanInfo)
myParseHsExp = parseResultToEither . parseExpWithMode myDefaultParseMode2

flame :: QuasiQuoter
flame = QuasiQuoter { quoteExp = \str -> case myParseExp str of
        Right (DoE Nothing ss) -> return (go ss)
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
