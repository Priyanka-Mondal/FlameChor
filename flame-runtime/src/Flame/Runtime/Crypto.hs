{-# LANGUAGE ViewPatterns, FlexibleInstances, ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable, DeriveFunctor, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses, OverloadedStrings #-}
module Flame.Runtime.Crypto where

import Control.Monad

import Flame.Runtime.Crypto.Util (chunksOf)
import Flame.Runtime.Crypto.KeyMap
import Flame.Runtime.Principals

import Crypto.PubKey.RSA
import Crypto.PubKey.RSA.OAEP
import Crypto.PubKey.RSA.PSS
import Crypto.Hash.Algorithms
import qualified Data.Map as M
import Control.Monad.IO.Class
import Control.Exception
import Control.Monad
import Data.Maybe (catMaybes,fromJust,isJust)

import qualified Data.ByteString.Char8 as B
import qualified Data.Map as M
import qualified Data.Set as S

import Crypto.Cipher.AES (AES256)
import Crypto.Cipher.Types
import Crypto.MAC.HMAC
import Crypto.Error (CryptoFailable(..))
import Crypto.Random
import qualified Data.ByteString.Base64 as B64

import Debug.Trace


class Serializable a where
  serialize :: a -> B.ByteString
  deserialize :: B.ByteString -> Either String a

instance Serializable PublicKey where
  serialize pk = B64.encode (B.pack (show pk))
  deserialize b =
    case B64.decode b of
      Right b' ->
        case reads (B.unpack b') of
          [(pk,_)] -> Right pk
          _ -> Left "PublicKey deserialize error"
      Left err -> Left err

instance Serializable PrivateKey where
  serialize sk = B64.encode (B.pack (show sk))
  deserialize b =
    case B64.decode b of
      Right b' ->
        case reads (B.unpack b') of
          [(sk,_)] -> Right sk
          _ -> Left "PrivateKey deserialize error"
      Left err -> Left err

instance Serializable B.ByteString where
  serialize b = B64.encode b
  deserialize b = B64.decode b

instance (Serializable a, Serializable b) => Serializable (a,b) where
  serialize (a,b) = B.pack $ show (serialize a, serialize b)
  deserialize s = case reads (B.unpack s) of
                    [((a,b),_)] -> do a' <- deserialize a
                                      b' <- deserialize b
                                      return (a',b')
                    _ -> Left "Pair deserialize error"

instance (Serializable a) => Serializable [a] where
  serialize as = "[" `B.append` B.intercalate "," (map serialize as) `B.append` "]"
  deserialize b =
    case B.stripPrefix "[" b of
      Just b' ->
        case B.stripSuffix "]" b' of
          Just b'' ->
            case B.split ',' b'' of
              bs -> mapM deserialize bs
          _ -> Left "List deserialize error"
      _ -> Left "List deserialize error"
-- | AES key size in bytes
aesKeySize :: Int
aesKeySize = 32
-- | AES IV size
aesIVSize :: Int
aesIVSize = 16

cipherInitNoErr :: (Cipher c, BlockCipher c) => Key c -> c
cipherInitNoErr (Key k) = case cipherInit k of
      CryptoPassed a -> a
      CryptoFailed e -> error (show e)
          
cipherMakeKey :: Cipher cipher => cipher -> B.ByteString -> SymKey 
cipherMakeKey _ = Key

-- | RSA key size in bytes
rsaKeySize = 128

-- | Exponent required to generate RSA key pairs. Using a value
-- recommended by cryptonite docs.
magicExponent = 0x10001


class Encrypt pk where
  flameEncrypt :: pk -> B.ByteString -> IO B.ByteString
class Decrypt sk where
  flameDecrypt :: sk -> B.ByteString -> B.ByteString
  
defaultOAEPParamsSHA256 :: OAEPParams SHA256 B.ByteString B.ByteString
defaultOAEPParamsSHA256 = defaultOAEPParams SHA256

defaultPSSParamsSHA256 :: PSSParams SHA256 B.ByteString B.ByteString
defaultPSSParamsSHA256 = defaultPSSParams SHA256



instance (BlockCipher cipher, Cipher cipher) => Encrypt (Key cipher) where
  flameEncrypt k m = do r <- getRandomBytes aesIVSize
                        let Just msgIV = makeIV (r :: B.ByteString)
                        let ctx = cipherInitNoErr k
                            enc = ctrCombine ctx msgIV m
                        return (r `B.append` enc)

instance (BlockCipher cipher, Cipher cipher) => Decrypt (Key cipher) where
  flameDecrypt k m = let (r,actualm) = B.splitAt aesIVSize m
                         Just msgIV = makeIV (r :: B.ByteString)
                         ctx = cipherInitNoErr k
                     in ctrCombine ctx msgIV actualm

{- onion crypto -}
instance Encrypt a => Encrypt [a] where
  flameEncrypt pks v = chainCryptoM flameEncrypt v pks
instance Decrypt a => Decrypt [a] where
  flameDecrypt sks b = chainCrypto flameDecrypt b (reverse sks)

chainCryptoM f b ks = foldM (\ct k -> f k ct) b ks
chainCrypto f b ks = foldl (\ct k -> f k ct) b ks

--flameSign:: MonadRandom m => sk -> B.ByteString -> m (Either Error B.ByteString)
flameSign sk v = signSafer defaultPSSParamsSHA256 sk v

flameVerify pk m sig = verify defaultPSSParamsSHA256 pk m sig

{- multiple signatures -}
flameMultiSign sks v = mapM (\sk -> do Right s <- flameSign sk v; return s) sks
--flameMultiVerify pks v sigs = all (\(pk,sig) -> flameVerify pk v sig) (zip pks sigs)

{- | Generates two RSA key pairs, one for encryption and another for
   signatures.
-}
generateKeyPairs :: IO KeyPairs
generateKeyPairs =
  do enckp <- liftIO $ generate rsaKeySize magicExponent
     sigkp <- liftIO $ generate rsaKeySize magicExponent
     return (mkFullKeyPairs enckp sigkp)

{- | Fetches the RSA public/private key pair for the given principal in the
  CLIO key map. 
  Sanity check: never call before checking the store
fetchKeyPairPrin :: Prin -> IO KeyPairs
fetchKeyPairPrin p =
  CLIO $ do km <- getKeyMap
            case M.lookup p km of
              Just keypair -> return keypair
              Nothing -> fail $ "No KeyPairs for principal " ++ show p
-}

rsaEncryptArbSize :: PublicKey -> B.ByteString -> IO B.ByteString
rsaEncryptArbSize pk m =
  do let chunkedm = chunksOf (rsaKeySize `div` 3) m
     encms <-
       mapM (\b -> do ee <- encrypt defaultOAEPParamsSHA256 pk b
                      case ee of
                        Left err -> fail (show err)
                        Right e -> return e) chunkedm
     return (serialize encms)

rsaDecryptArbSize :: PrivateKey -> B.ByteString -> IO B.ByteString
rsaDecryptArbSize sk m =
   case deserialize m of
     Right bs ->
       do ps <- mapM (\b -> decryptSafer defaultOAEPParamsSHA256 sk b) bs
          if any isLeft ps
            then fail "decryption error"
            else return $ B.concat [r | Right r <- ps]
  where isLeft (Left _) = True
        isLeft _ = False

rsaSignThenEncryptArbSize :: PublicKey -> PrivateKey -> B.ByteString -> IO B.ByteString
rsaSignThenEncryptArbSize epk ssk m =
  do Right sig <- flameSign ssk m
     let m' = serialize (m, sig)
     rsaEncryptArbSize epk m'

rsaDecryptThenVerifyArbSize :: PublicKey -> PrivateKey -> B.ByteString -> IO B.ByteString
rsaDecryptThenVerifyArbSize spk esk m =
  do m' <- rsaDecryptArbSize esk m
     case deserialize m' of
       Right (m'', sig) | flameVerify spk m'' sig ->
                            return m''
       _ -> fail "Deserialization or verification error in rsaDecryptThenVerifyArbSize"

instance Serializable (Key AES256) where
  serialize (Key k) = serialize k
  deserialize b = case deserialize b of
    Left e -> Left e
    Right k -> Right (cipherMakeKey (undefined :: AES256) k)

{-
fetchKeyPairsCategory :: [Prin] -> IO [KeyPairs]
fetchKeyPairsCategory [] = return []
fetchKeyPairsCategory (p:ps) =
  do xs <- ((:[]) <$> fetchKeyPairPrin p) `catchCLIO`
       (\(e :: SomeException) -> return [])
     ps' <- fetchKeyPairsCategory ps
     return (xs ++ ps')
-}

allPairs :: [a] -> [b] -> [(a,b)]
allPairs xs ys = [ (x,y) | x <- xs, y <- ys ]

{-
fetchCK :: Disjunction -> IO (Maybe (SymKey,KeyPairs))
fetchCK d =
  do r <- clioRedisGet (B.pack $ show d)
     case r of
       Right (Just m) ->
         do let Right (publics, (ct, sig)) = deserialize m
                Right (epk,spk) = deserialize publics
            kps <- fetchKeyPairsCategory (S.toAscList $ dToSet d)
            let spks = concatMap (\kp ->
                        case hasVerificationKey kp of
                          Just k -> [k]
                          Nothing -> []) kps
            if any (\k -> clioVerify k (serialize (publics, ct)) sig) spks
              then do let esks = concatMap (\kp ->
                                        case hasDecryptionKey kp of
                                          Just k -> [k]
                                          Nothing -> []) kps
                          Right cts = deserialize ct
                      ps <- mapM (\(esk,b) ->
                                    (Just <$> rsaDecryptArbSize esk b) `catchCLIO` (\(e::SomeException) -> return Nothing)) (allPairs esks cts) -- hacky!
                      let xs = catMaybes ps
                      when (null xs) $ do
                        km <- CLIO getKeyMap
                        fail $ "category key decryption failure: no valid decryption keys available for " ++ show d ++ " in keymap for principals " ++ show (M.keys km)
                      let secrets = head xs
                      let Right (symkey, (esk, ssk)) = deserialize secrets
                      return (Just (symkey, mkFullKeyPairs (epk,esk) (spk,ssk)))
              else do
                km <- CLIO getKeyMap
                fail $ "category key verification failure: no valid verification keys available for " ++ show d ++ " in keymap for principals " ++ show (M.keys km)
       _ -> return Nothing
       where isRight (Right _) = True
             isRight _ = False

isSingletonPrin d = S.size (dToSet d) == 1

generateKeysD :: Disjunction -> IO (SymKey, KeyPairs)
generateKeysD d =
  do kps <- if (isSingletonPrin d)
            then fetchKeyPairPrin (S.findMin (dToSet d))
            else CLIO generateKeyPairs
     symkey <- getRandomBytes aesKeySize
     return (cipherMakeKey (undefined :: AES256) symkey, kps)

fetchKeysD :: Disjunction -> IO (SymKey, KeyPairs)
fetchKeysD d =
  do mck <- fetchCK d
     case mck of
       Just (symkey, kps) -> {- update local keymap if needed -} return (symkey, kps)
       Nothing -> -- assumes: there is at least one signing key in the keymap
         do (symkey, kps@(allKeys -> (epk,esk,spk,ssk))) <- generateKeysD d
            let secrets = serialize (symkey, (esk, ssk))
                publics = serialize (epk,spk)
            let ps =  S.toAscList (dToSet d)
            cts <- forM ps $ \p ->
              -- encrypt the secrets with PKs of each of the
              -- principals in the category
              do (hasEncryptionKey -> Just principalPK) <- fetchKeyPairPrin p 
                 rsaEncryptArbSize principalPK secrets
            let ct = serialize cts
            let pubm = serialize (publics, ct)
            sig <- foldM (\s p ->
                            do (hasSigningKey -> principalSK) <-
                                 fetchKeyPairPrin p
                               case principalSK of
                                 Nothing  -> {- not a signing principal -} return s
                                 Just ssk -> do Right newsig <- (putStrLn ("Signed by " ++ show p)) >> clioSign ssk pubm
                                                return newsig) errMsg ps
                                  -- write everything to the store
            let m = serialize (publics, (ct, sig))
            putStrLn $ "Storing entry for category " ++ (show d)
            clioRedisSet (B.pack $ show d) m
            return (symkey, kps)
       where errMsg = error $ "no principal in keymap able to sign category " ++ show d

fetchVerifKeysD :: Disjunction -> IO KeyPair
fetchVerifKeysD d | isSingletonPrin d = signKP <$> fetchKeyPairPrin (S.findMin (dToSet d))
fetchVerifKeysD d =
  do r <- clioRedisGet (B.pack $ show d)
     case r of
       Right (Just m) ->
         do let Right (publics, (ct, sig)) = deserialize m :: Either String (B.ByteString, (B.ByteString, B.ByteString))
                Right (epk,spk) = deserialize publics :: Either String (PublicKey, PublicKey)
            kps <- fetchKeyPairsCategory (S.toAscList $ dToSet d)
            let spks = concatMap (\kp ->
                        case hasVerificationKey kp of
                          Just k -> [k]
                          Nothing -> []) kps
            if any (\k -> clioVerify k (serialize (publics, ct)) sig) spks
              then return (KeyPair (Just spk) Nothing)
              else do
                km <- CLIO getKeyMap
                fail $ "category key verification failure: no valid verification keys available for " ++ show d ++ " in keymap for principals " ++ show (M.keys km)
       _ -> fail $ "Unable to fetch public keys for non-existing category " ++ show d
       where isRight (Right _) = True
             isRight _ = False

fetchSymKeysFor :: DCLabel -> IO [SymKey]
fetchSymKeysFor l = map fst <$> fetchKeyPairsFor (dcSecrecy l)

fetchKeyPairsFor :: CNF -> IO [(SymKey,KeyPairs)]
fetchKeyPairsFor cnf =
     mapM fetchKeysD (S.toList $ cToSet cnf)

fetchVerifKeyPairsFor :: CNF -> IO [KeyPair]
fetchVerifKeyPairsFor cnf =
     mapM fetchVerifKeysD (S.toList $ cToSet cnf)

fetchEncryptionKeysFor :: DCLabel -> IO [PublicKey]
fetchEncryptionKeysFor l = map (publicKey . encKP . snd) <$> fetchKeyPairsFor (dcSecrecy l)

fetchDecryptionKeysFor :: DCLabel -> IO [PrivateKey]
fetchDecryptionKeysFor l = map (privateKey . encKP . snd) <$> fetchKeyPairsFor (dcSecrecy l)

fetchSignatureKeysFor  :: DCLabel -> IO [PrivateKey]
fetchSignatureKeysFor l = map (privateKey . signKP . snd) <$> fetchKeyPairsFor (dcIntegrity l)

fetchVerificationKeysFor  :: DCLabel -> IO [PublicKey]
fetchVerificationKeysFor l =
  map publicKey <$> fetchVerifKeyPairsFor (dcIntegrity l)

initializeKeyMap :: [Prin] -> IO KeyMap
initializeKeyMap ps =
  do mapM_ fetchKeyPairPrin ps
     CLIO $ getKeyMap

initializeKeyMapIO :: [Prin] -> IO KeyMap
initializeKeyMapIO ps =
  do kps <- mapM (\p -> do
                        ekp <- generate rsaKeySize magicExponent
                        skp <- generate rsaKeySize magicExponent
                        return (p, mkFullKeyPairs ekp skp)) ps
     return (foldr (uncurry M.insert) M.empty kps)
-}