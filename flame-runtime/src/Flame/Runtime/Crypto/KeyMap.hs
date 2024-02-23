{-# LANGUAGE ViewPatterns, GADTs #-}
module Flame.Runtime.Crypto.KeyMap where

import Crypto.PubKey.RSA
import Crypto.Cipher.AES (AES256)
import qualified Data.ByteString.Char8 as B

import qualified Data.Map as M
import Data.Text      (Text)

import Flame.Runtime.Principals

--type KeyPair  = (PublicKey, PrivateKey)
data KeyPairs = KP { hasEncKP :: Maybe KeyPair, hasSignKP :: Maybe KeyPair } deriving (Show)
data KeyPair = KeyPair { hasPublicKey :: Maybe PublicKey, hasPrivateKey :: Maybe PrivateKey } deriving (Show)

type KeyMap =  M.Map Text KeyPairs

data Key cipher = Key B.ByteString
type SymKey = Key AES256

publicKey :: KeyPair -> PublicKey
publicKey (KeyPair { hasPublicKey = Just pk }) = pk
privateKey :: KeyPair -> PrivateKey
privateKey (KeyPair { hasPrivateKey = Just sk }) = sk

encKP :: KeyPairs -> KeyPair
encKP (hasEncKP -> Just kp) = kp
signKP :: KeyPairs -> KeyPair
signKP (hasSignKP -> Just kp) = kp

fullKeyPair :: KeyPair -> (PublicKey, PrivateKey)
fullKeyPair (KeyPair (Just pk) (Just sk)) = (pk,sk)

mkFullKeyPair :: PublicKey -> PrivateKey -> KeyPair
mkFullKeyPair pk sk = KeyPair (Just pk) (Just sk)

allKeys :: KeyPairs -> (PublicKey, PrivateKey, PublicKey, PrivateKey)
allKeys (KP (Just (fullKeyPair -> (epk,esk))) (Just (fullKeyPair -> (spk, ssk)))) =
  (epk, esk, spk, ssk)

mkFullKeyPairs :: (PublicKey,PrivateKey) -> (PublicKey,PrivateKey) -> KeyPairs
mkFullKeyPairs (epk, esk) (spk, ssk) = KP (Just $ mkFullKeyPair epk esk) (Just $ mkFullKeyPair spk ssk)

hasEncryptionKey :: KeyPairs -> Maybe PublicKey
hasEncryptionKey (hasEncKP -> Just (hasPublicKey -> Just pk)) = Just pk
hasEncryptionKey _ = Nothing

hasDecryptionKey :: KeyPairs -> Maybe PrivateKey
hasDecryptionKey (hasEncKP -> Just (hasPrivateKey -> Just sk)) = Just sk
hasDecryptionKey _ = Nothing

hasVerificationKey :: KeyPairs -> Maybe PublicKey
hasVerificationKey (hasSignKP -> Just (hasPublicKey -> Just pk)) = Just pk
hasVerificationKey _ = Nothing

hasSigningKey :: KeyPairs -> Maybe PrivateKey
hasSigningKey (hasSignKP -> Just (hasPrivateKey -> Just sk)) = Just sk
hasSigningKey _ = Nothing

data KeySpec k where
  EncryptionKey :: KeySpec PublicKey
  DecryptionKey :: KeySpec PrivateKey
  VerificationKey :: KeySpec PublicKey
  SigningKey :: KeySpec PrivateKey

adjustKey :: Text -> KeySpec k -> Maybe k -> KeyMap -> KeyMap
adjustKey p EncryptionKey mpk km =
  M.adjust (\kp -> kp { hasEncKP = Just $ (encKP kp) { hasPublicKey = mpk } }) p km
adjustKey p DecryptionKey msk km =
  M.adjust (\kp -> kp { hasEncKP = Just $ (encKP kp) { hasPrivateKey = msk } }) p km
adjustKey p VerificationKey mpk km =
  M.adjust (\kp -> kp { hasSignKP = Just $ (signKP kp) { hasPublicKey = mpk } }) p km
adjustKey p SigningKey msk km =
  M.adjust (\kp -> kp { hasSignKP = Just $ (signKP kp) { hasPrivateKey = msk } }) p km

{- | Left-biased keymap merge
-}
(<+>) :: KeyMap -> KeyMap -> KeyMap
a <+> b = a `M.union` b
