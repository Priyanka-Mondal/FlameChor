{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE  RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
module MyHasChor.Choreography.Flaqr where

import MyHasChor.Choreography.Location
import MyHasChor.Control.Monad.Freer
import Control.Monad.IO.Class
import Control.Concurrent.Async
import Prelude hiding (compare)
import System.Timeout 
--import Main (NodeState)
import Flame.Principals
import Flame.TCB.Freer.IFC
    ( type (!),
      Labeled,
      bind,
      label,
      use,
      protect,
      join,
      restrict,
      runLabeled,
      relabel' )
import Flame.Assert

--data NodeState = INIT | PREPREPARE | PREPARE | COMMIT | COMMITTED
--  deriving (Eq, Show, Ord, Read) 

class HasFail a where
  failVal :: a

instance HasFail Int where
  failVal = -1

instance HasFail String where
  --failVal :: String
  failVal = "fail"

--instance HasFail NodeState where
--  failVal = INIT


time :: Int 
time = 10000000

--simple select between 2 values
select :: (HasFail a, Eq a) => Async a -> Async a -> IO (Async a)
select a b = do
    a' <- timeout time (wait a)
    case a' of 
      (Just e) | e /= failVal -> return a
      _ -> do
         b' <- timeout time (wait b)
         case b' of 
          (Just e) -> return b
          Nothing -> async (return failVal)

{--selecT :: (HasFail a, Eq a) =>[(Async a)] -> IO (Async a)
selecT [] = error "ERROR: Empty list of asynchronous computations."
selecT [a] =  do 
 -- a'<- a 
  select2' a
selecT (a:as) = do 
   a''<- wait a 
   a' <- (timeout time (wait a))
   case a' of 
      (Just e) | (e /= failVal) -> return a
      _ ->  (selecT as)--}
 
selecT ::  (HasFail a, Eq a) => IO ([IO (Async a)])  -> IO (Async a)
selecT as = do 
  as' <- as 
  select_ as'
  
--select one from the given list
select_ :: (HasFail a, Eq a) =>[IO (Async a)] -> IO (Async a)
select_ [] = error "ERROR: Empty list of asynchronous computations."
select_ [a] =  do 
  a'<- a 
  select' a'
select_ (a:as) = do 
   a''<- a 
   a' <- timeout time (wait a'')
   case a' of 
      (Just e) | e /= failVal -> return a''
      _ ->  select_ as
 
{--select2' :: (HasFail a, Eq a) => Async a -> IO (Async a)
select2' a = do
    a' <- timeout time (wait a)
    case a' of 
      (Just e) | (e /= failVal) -> return a
      _ -> (async (return failVal))--}


--select of one value, i.e. returns fail when that one value is not avaialable
select' :: (HasFail a, Eq a) => Async a -> IO (Async a)
select' a = do
    a' <- timeout time (wait a)
    case a' of 
      (Just e) | e /= failVal -> return a
      _ -> async (return failVal)

combinations :: Int -> [a] -> [[a]]
combinations 0 _  = [[]]
combinations _ [] = []
combinations n (x:xs) = [ x:rest | rest <- combinations (n-1) xs ] ++ combinations n xs


-- compare between i elements from the list of given async values
compare_ :: forall a. (Ord a, HasFail a) => [Async a] -> Int -> IO ([IO (Async a)])
compare_ xs i = return (map comparec com) --was ((map comparec) com) then hlint gave error 
  where 
    com = combinations i xs

comparec :: forall a. (Ord a, HasFail a) => [Async a] -> IO (Async a)
comparec [] = error "ERROR: Empty list of asynchronous computations."
comparec [a] = compare'' a
comparec (x:ys) = compare' x ys 

--comapare of one value, equivalent to select of one value
compare'' :: (HasFail a, Eq a) => Async a -> IO (Async a)
compare'' = select'

compare' :: forall a. (Ord a, HasFail a) => Async a -> [Async a] -> IO (Async a)
compare' x [y] = compare x y
compare' x (y:ys) = do 
    a' <- timeout time (wait x)
    case a' of 
      (Just e) | e /= failVal -> do 
         b' <- timeout time (wait y)
         case b' of 
          (Just e') -> if e == e' then compare' x ys else async (return failVal)
          Nothing -> async (return failVal)
      _ -> async (return failVal)

--simple compare between 2 values 
compare :: forall a. (Ord a, HasFail a) => Async a -> Async a -> IO (Async a)
compare a b = do
    a' <- timeout time (wait a)
    case a' of 
      (Just e) | e /= failVal -> do 
         b' <- timeout time (wait b)
         case b' of 
          (Just e') -> if e == e' then return b else async (return failVal)
          Nothing -> async (return failVal)
      _ -> async (return failVal)


com:: forall a. (Ord a, HasFail a) => Async a -> Async a -> IO (Async a)
com a b = do
    a' <- timeout time (wait a)
    case a' of 
      (Just e) | e /= failVal -> do 
         b' <- timeout time (wait b)
         case b' of 
          (Just e') -> if e == e' then return b else async (return failVal)
          Nothing -> async (return failVal)
      _ -> async (return failVal)


getLargest :: forall a. (Num a, Read a, Ord a, HasFail a) => Async a -> Async a -> IO (Async a) 
getLargest a b = do 
 z <- timeout 10000000 (waitBoth a b)
 case z of 
  Nothing -> async (return failVal)
  Just (x,y) -> if x > y then return a else return b


--  Expected: Labeled IO ABC (ABC ! Async a0)
--     Actual: IO (Async a2)

-- sCompare  :: SPrin pc -> IO (Async Int) -> Labeled IO pc (pc ! Async Int)
-- sCompare  pc a = restrict pc (\_ -> a)
