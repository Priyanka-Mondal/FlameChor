module Choreography.Flaqr where

import Choreography.Location
import Control.Monad.Freer
import Control.Monad.IO.Class
import Control.Concurrent.Async
import Prelude hiding (compare)
import System.Timeout 

class HasFail a where
  failVal :: a

instance HasFail Int where
  failVal = -1

instance HasFail String where
  failVal = "fail"

time :: Int 
time = 10000000


select :: (HasFail a, Eq a) => Async a -> Async a -> IO (Async a)
select a b = do
    a' <- timeout time (wait a)
    case a' of 
      (Just e) | (e /= failVal) -> return a
      _ -> do
         b' <- timeout time (wait b)
         case b' of 
          (Just e) -> return b
          Nothing -> (async (return failVal))

select_ :: (HasFail a, Eq a) =>[IO (Async a)] -> IO (Async a)
select_ [] = error "ERROR: Empty list of asynchronous computations."
select_ [a] =  do 
  a'<- a 
  select' a'
select_ (a:as) = do 
   a''<- a 
   a' <- timeout time (wait a'')
   case a' of 
      (Just e) | (e /= failVal) -> return a''
      _ ->  (select_ as)
 
select' :: (HasFail a, Eq a) => Async a -> IO (Async a)
select' a = do
    a' <- timeout time (wait a)
    case a' of 
      (Just e) | (e /= failVal) -> return a
      _ -> (async (return failVal))

combinations :: Int -> [a] -> [[a]]
combinations 0 _  = [[]]
combinations _ [] = []
combinations n (x:xs) = [ x:rest | rest <- combinations (n-1) xs ] ++ combinations n xs


compare_ :: forall a. (Ord a, HasFail a) => [Async a] -> Int -> IO ([IO (Async a)])
compare_ xs i = return ((map comparec) com)
  where 
    com = combinations i xs

comparec :: forall a. (Ord a, HasFail a) => [Async a] -> IO (Async a)
comparec [] = error "ERROR: Empty list of asynchronous computations."
comparec [a] = compare'' a
comparec (x:ys) = compare' x ys 

compare'' :: (HasFail a, Eq a) => Async a -> IO (Async a)
compare'' a = select' a

compare' :: forall a. (Ord a, HasFail a) => (Async a) -> [Async a] -> IO (Async a)
compare' x [y] = compare x y
compare' x (y:ys) = do 
    a' <- timeout time (wait x)
    case a' of 
      (Just e) | (e /= failVal) -> do 
         b' <- timeout time (wait y)
         case b' of 
          (Just e') -> if (e == e') then (compare' x ys) else async (return failVal)
          Nothing -> async (return failVal)
      _ -> async (return failVal)

compare :: forall a. (Ord a, HasFail a) => Async a -> Async a -> IO (Async a)
compare a b = do
    a' <- timeout time (wait a)
    case a' of 
      (Just e) | (e /= failVal) -> do 
         b' <- timeout time (wait b)
         case b' of 
          (Just e') -> if (e == e') then return b else async (return failVal)
          Nothing -> async (return failVal)
      _ -> async (return failVal)


getLargest :: forall a. (Num a, Read a, Ord a, HasFail a) => Async a -> Async a -> IO (Async a) 
getLargest a b = do 
 z <- timeout 10000000 (waitBoth a b)
 case z of 
  Nothing -> async (return failVal)
  Just (x,y) -> if x > y then (return a) else (return b)