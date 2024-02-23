module Flame.Runtime.Crypto.Util (chunksOf) where

import qualified Data.ByteString.Char8 as B

build g = g (:) []

chunksOf :: Int -> B.ByteString -> [B.ByteString]
chunksOf i b = map (B.take i) (build (splitter b)) where
  splitter :: B.ByteString -> (B.ByteString -> a -> a) -> a -> a
  splitter b c n | B.null b = n
                 | otherwise = b `c` splitter (B.drop i b) c n
