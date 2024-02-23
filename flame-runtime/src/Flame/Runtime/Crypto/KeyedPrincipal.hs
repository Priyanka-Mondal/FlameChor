{-# LANGUAGE ViewPatterns, GADTs #-}
{-# LANGUAGE DeriveGeneric, DefaultSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
-- {-# OPTIONS_GHC -fplugin Flame.Solver #-}

module Flame.Runtime.Crypto.KeyedPrincipal where

import qualified Data.Map as M
import Flame.Principals
import Flame.Runtime.Principals
import Flame.TCB.IFC
import Flame.Runtime.Crypto
import Flame.Runtime.Crypto.KeyMap
import qualified Data.ByteString.Char8 as B
import Data.Text      (Text)
import qualified Data.Text.Encoding as TE
import Crypto.Random.Types
import Data.Either
import Data.List
import GHC.Generics
import qualified Data.Serialize as S

import Crypto.PubKey.RSA
import Crypto.PubKey.RSA.OAEP
import Crypto.PubKey.RSA.PSS
import Crypto.Hash.Algorithms
import qualified Data.Map as M
import Control.Monad.IO.Class
import Control.Exception
import Control.Monad
import Control.Monad.State (runStateT, StateT, get, put)

import Crypto.Cipher.AES (AES256)
import Crypto.Cipher.Types
import Crypto.MAC.HMAC
import Crypto.Error (CryptoFailable(..))
import Crypto.Random

-- all names in prin are guaranteed to be in keys
data KeyedPrin p = UnsafeKey { prin :: DPrin p, keys :: KeyMap} 
(<=>) :: DPrin p -> KeyMap -> KeyedPrin p
p <=> km = UnsafeKey p km

instance S.Serialize Text where
    put = S.put . TE.encodeUtf8
    get = TE.decodeUtf8 <$> S.get 

deriving instance Generic Prin

instance S.Serialize Prin where {}

data IntegStruct = 
  NoSig Prin
  | SigBase Prin B.ByteString
  | SigConj Prin IntegStruct Prin IntegStruct
  | SigDisj Prin IntegStruct
 deriving Generic

instance S.Serialize IntegStruct where {}

data ConfStruct = 
  NoEnc Prin B.ByteString      -- plaintext
  | ConfBase Prin B.ByteString -- decrypts to plaintext
  | ConfCons Prin B.ByteString -- decrypts to ConfStruct
 deriving Generic

instance S.Serialize ConfStruct where {}

type EncSymKeyMap = M.Map Text B.ByteString 

data ProtectStruct = Protect { symKeys :: EncSymKeyMap, conf :: ConfStruct, integ :: IntegStruct }
  deriving Generic

instance S.Serialize ProtectStruct where {}

instance Serializable IntegStruct where
  serialize = S.encode
  deserialize = S.decode

instance Serializable ConfStruct where
  serialize = S.encode
  deserialize = S.decode

instance Serializable ProtectStruct where
  serialize = S.encode
  deserialize = S.decode

instance Serializable Text where
  serialize = S.encode
  deserialize = S.decode

writeFile :: (Serializable a, IFC m IO n, pc ⊑ l) => FilePath -> KeyedPrin l -> n l a -> m IO n pc l' ()
writeFile filename l plaintext = unsafeProtect $ do
  res <- exportVal l plaintext
  case res of
    Left err -> fail ("Failed to export to file: \n" ++ err) 
    Right ciphertext -> label <$> B.writeFile filename ciphertext

readFile :: (Serializable a, IFC m IO n) => FilePath -> KeyedPrin l -> m IO n pc l a
readFile filename l = unsafeProtect $ do
  ciphertext <- B.readFile filename
  res <- importVal l ciphertext
  case res of
    Left err -> fail ("Failed to import from file: \n" ++ err) 
    Right val -> return val

exportVal :: (Serializable a, Labeled n) => KeyedPrin l -> n l a ->  IO (Either String B.ByteString)
exportVal (UnsafeKey l keys) m' = do
   let m = serialize (unsafeUnlabel m')
   Right msigs <- sign (dyn l) m
   (Right mct, symKeys) <- runStateT (encrypt (dyn l) m) M.empty
   encSymKeys <- forM (M.toAscList symKeys) protectSymKey
   if all isRight encSymKeys 
    then
     let esks = M.fromList $ rights encSymKeys in
       return $ Right $ serialize $ Protect esks mct msigs
    else
     return $ Left $ intercalate "\n" $ lefts encSymKeys
     
 where
  protectSymKey :: (Text, SymKey) -> IO (Either String (Text, B.ByteString))
  protectSymKey (n, symkey) = 
    let mpk = do kps <- M.lookup n keys
                 kp  <- hasEncKP kps
                 hasPublicKey kp in
    case mpk of
      Just pk -> do ct <- rsaEncryptArbSize pk (serialize symkey)
                    return $ Right (n, ct)
      Nothing -> return $ Left ("Could not find encryption key for " ++ show n)

  encrypt :: Prin -> B.ByteString -> StateT (M.Map Text SymKey) IO (Either String ConfStruct)
  encrypt p m = 
   case p of
     Bot      -> return $ Right $ NoEnc Bot m
     Integ q  -> return $ Right $ NoEnc (Integ q) m
     Top      -> return $ Left "Attempted to encrypt for ⊤" -- Nobody can decrypt Top
     Conf p  -> encrypt p m
     Name n   -> do symKeys <- get
                    case M.lookup n symKeys of
                      Just symkey -> liftIO $ (flameEncrypt symkey m) >>= (\ct -> return $ Right $ ConfBase (Name n) ct)
                      Nothing -> do -- generate new symmetric key, use it and put it in state.
                                   symKeys <- get
                                   bytes <- liftIO $ getRandomBytes aesKeySize
                                   let symkey = (cipherMakeKey (undefined :: AES256) bytes)
                                   put $ M.insert n symkey symKeys
                                   liftIO $ (flameEncrypt symkey m) >>= (\ct -> return $ Right $ ConfBase (Name n) ct)
     Conj a b -> do mbct <- encrypt b m
                    case mbct of
                      Right bct  -> encrypt a (serialize bct)
                      Left error -> return $ Left error
     Disj a b -> do
       mbct <- encrypt b m
       mact <- encrypt a m
       case (mact, mbct) of
         (_, Right bct) -> return $ Right $ ConfCons b (serialize bct)
         (Right act, _) -> return $ Right $ ConfCons a (serialize act)
         (Left amsg, Left bmsg) -> return $ Left (amsg ++ "\n" ++ bmsg)

  sign :: Prin -> B.ByteString -> IO (Either String IntegStruct)
  sign p m = 
   case p of
     Bot      -> return (Right $ NoSig Bot)
     Conf q   -> return (Right $ NoSig (Conf q))
     Top      -> return (Left "Attempted to sign for ⊤") -- Nobody can sign with Top's integrity
     Integ p  -> sign p m
     Name n   -> let msk = do kps <- M.lookup n keys
                              kp  <- hasSignKP kps
                              hasPrivateKey kp in
                 case msk of
                   Just sk -> do esig <- flameSign sk m 
                                 case esig of 
                                   Right sig -> return $ Right $ SigBase (Name n) sig
                                   Left error -> return $ Left (show error)
                   Nothing -> return $ Left ("Could not find signing key for " ++ show n)
     Conj a b -> do
       asig' <- sign a m
       bsig' <- sign b m
       case (asig', bsig') of
         (Right asig, Right bsig) -> return $ Right $ SigConj a asig b bsig
         (Left amsg, Left bmsg) -> return $ Left (amsg ++ "\n" ++ bmsg)
         (_, Left bmsg) -> return $ Left bmsg
         (Left amsg, _) -> return $ Left amsg
     Disj a b -> do
       asig' <- sign a m
       bsig' <- sign b m
       case (asig', bsig') of
         (Right asig, _) -> return $ Right $ SigDisj (Disj a b) asig
         (_, Right bsig) -> return $ Right $ SigDisj (Disj a b) bsig
         (Left amsg, Left bmsg) -> return $ Left (amsg ++ "\n" ++ bmsg)

importVal :: forall a n l. (Serializable a, Labeled n) => KeyedPrin l -> B.ByteString -> IO (Either String (n l a))
importVal (UnsafeKey l keys) bytes =
  case deserialize bytes of 
    Right val -> do
        sks <- forM (M.toAscList (symKeys val)) decryptSymKey
        if all isRight sks 
         then
          let syms = M.fromList $ rights sks in
          case decrypt (dyn l) syms (conf val) of
             Right m -> return $ Right $ label m
             Left err -> return $ Left err
         else
          return $ Left $ intercalate "\n" $ lefts sks
    Left err -> return $ Left err
  where
    decryptSymKey :: (Text, B.ByteString) -> IO (Either String (Text, SymKey))
    decryptSymKey (n, bs) =
      let msk = do kps <- M.lookup n keys
                   kp  <- hasEncKP kps
                   hasPrivateKey kp in
      case msk of
        Just sk -> do mm <- deserialize <$> rsaDecryptArbSize sk bs
                      case mm of
                        Right m -> return $ Right (n, m)
                        Left err -> return $ Left err
        Nothing -> return $ Left ("Could not find decryption key for " ++ show n)

    decrypt :: Prin -> M.Map Text SymKey -> ConfStruct -> Either String a
    decrypt p symKeys c =
      case c of
        NoEnc q m | p == q -> deserialize m
        ConfBase (Name n) c | p == (Name n) -> 
          case M.lookup n symKeys of
            Just symkey -> deserialize $ flameDecrypt symkey c
            _ -> Left ("Could not find symmetric encryption key for " ++ show n)

    verify :: Prin -> B.ByteString -> IntegStruct -> Bool
    verify p m sig = case sig of
                       NoSig q | p == q -> True
                       SigBase (Name n) sig | p == (Name n) -> 
                         let mpk = do kps <- M.lookup n keys 
                                      kp  <- hasSignKP kps
                                      hasPublicKey kp in
                         case mpk of
                           Just pk -> flameVerify pk m sig
                       SigConj q sigq r sigr | (p == (Conj q r)) ->
                         verify q m sigq && verify r m sigr 
                       SigDisj (Disj q r) sig | (p == (Disj q r)) ->
                         verify q m sig || verify r m sig 
                       _ -> False
                       
-- main :: IO ()
-- main = do 
--   let p = Name "Alice" in
--    withPrin p $ \(alice :: DPrin p) ->
--      do kps <- generateKeyPairs
--         let km = M.fromList [ ("Alice" :: Text, kps) ]
--             keyprin = UnsafeKey alice km
--             secret  = label "secret string" :: Lbl p Text
--         res <- exportVal keyprin secret
--         case res of
--           Left err -> putStrLn err
--           Right ct -> let out = (serialize ct) in
--                       do B.putStrLn out
--                          res <- importVal keyprin out
--                          case res of
--                            Right (v:: Lbl p Text) -> B.putStrLn "OK!?"
--                            Left err -> fail err
