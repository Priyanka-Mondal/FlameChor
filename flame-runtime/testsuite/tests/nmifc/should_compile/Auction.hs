{-# LANGUAGE TypeOperators, PostfixOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}

import Prelude hiding ( return, (>>=), (>>)
                      , print, putStr, putStrLn, getLine)
import qualified Prelude as P ( return, (>>=), (>>) )
import Data.List
import Data.Proxy
import Data.String
import Data.Maybe
import Flame.Runtime.Time
import Data.Time as T
import Data.ByteString.Char8 (ByteString, pack, unpack, empty)

import Flame.Principals
import Flame.Runtime.Prelude
import Flame.Runtime.Principals
import Flame.Runtime.IO
import Flame.IFC 
import qualified System.IO as SIO
import Data.IORef as SIO
import Flame.Runtime.FLARef as Ref

{- Static principals -}
alice = SName (Proxy :: Proxy "Alice")
type Alice = KName "Alice"
aliceBid :: Lbl Alice Int
aliceBid = label 4

bob = SName (Proxy :: Proxy "Bob")
type Bob = KName "Bob"
bobBid :: Lbl Bob Int
bobBid = label 3                                          

commit :: FLA m e n => SPrin p -> m e n (I p) (C p) a -> m e n (I p) p a
commit p v = assume ((SBot*←) ≽ (p*←)) (reprotect v)

receive :: FLA m e n => SPrin p -> SPrin q -> m e n (I q) p a -> m e n (I q) (p ∧ (I q)) a
receive p q v = assume (p ≽ (q*←)) (reprotect v)

{- does compile -}
bad_receive :: FLA m e n => SPrin p -> SPrin q -> m e n (I q) (p ∧ C q) a -> m e n (I q) (p ∧ q) a
bad_receive p q v = assume (p ≽ (q*←)) (reprotect v)

bad_open :: FLA m e n => SPrin p -> SPrin q -> m e n ((∇) p) (p ∧ q) a -> m e n ((∇) p) ((I p) ∧ q) a
bad_open p q v = assume ((*∇) (q) ≽ (*∇) (p)) $ assume ((q*→) ≽ (p*→)) (reprotect v)

open :: FLA m e n => SPrin p -> SPrin q -> m e n ((∇) p) (p ∧ (I q)) a -> m e n ((∇) p) (I (p ∧ q) ∧ C (p ∨ q)) a
open p q v = assume ((*∇) (q) ≽ (*∇) (p)) $ assume ((q*→) ≽ (p*→)) (reprotect v)

{- Forced to commit only public data. committing it makes it secret. -}
{- Alternative: with higher integrity pc, could declass, then endorse. -}
nm_commit :: (BFLA c m e n, p ⊑ Δ p) =>
             SPrin p
             -> c m e n (Δ KBot) (I p) KBot a
             -> c m e n (Δ KBot) (I p) p a
nm_commit p v = iassume ((SBot*←) ≽ (p*←)) (reprotect_b v)

nm_receive :: (BFLA c m e n, p ⊑ Δ p) =>
              SPrin p
              -> SPrin q
              -> c m e n (Δ p) (I q) p a -> c m e n (Δ p) (I q) (p ∧ (I q)) a
nm_receive p q v = iassume ((p*←) ≽ (q*←)) (reprotect_b v)

{- does not compile 
nm_badreceive :: (NMFLA m n, p ⊑ Δ p) =>
                 SPrin p
                 -> SPrin q
                 -> m n (Δ p) (I q) (p ∧ C q) a
                 -> m n (Δ p) (I q) (p ∧ q) a
nm_badreceive p q v = iassume ((p*←) ≽ (q*←)) (NM.reprotect (SEye p) v)
-}

nm_open :: BFLA c m e n =>
           SPrin p
           -> SPrin q
           -> c m e n (C q) ((∇) p) (p ∧ (I q)) a
           -> c m e n (C q) ((∇) p) (I (p ∧ q) ∧ C (p ∨ q)) a
nm_open p q v = vassume ((*∇) q ≽ (*∇) p) $
                 cassume ((q*→) ≽ (p*→)) (reprotect_b v)

flacAuction :: IO (Lbl SU ())
flacAuction =
  do
    abid_rcvd <- runIFC $ receive alice bob (lift aliceBid)
    bbid_rcvd <- runIFC $ receive bob alice (lift bobBid)
    abid_open <- runIFC $ open alice bob (lift abid_rcvd)
    bbid_open <- runIFC $ open bob alice (lift bbid_rcvd)
    let winner = bind abid_open $ \abid ->
                 bind bbid_open $ \bbid ->
                 if abid > bbid then
                   label "Alice wins" :: Lbl (I (Alice ∧ Bob) ∧ C (Alice ∨ Bob)) String
                 else if abid < bbid then
                   label "Bob wins" 
                 else 
                   label "Tie" in
      runIFC $ do ebind winner $ \win ->
                   hPutStrLn @_ @_ @(I (Alice ∧ Bob) ∧ C (Alice ∨ Bob)) output win
  where 
   output = mkStdout (((alice *∧ bob)*←) *∧ ((alice *∨ bob)*→))
   (>>=)  = (P.>>=)

badflacAuction :: IO (Lbl SU ())
badflacAuction =
  do
    bobAttackBid <- runIFC $ bobAttack
    abid_rcvd <- runIFC $ bad_receive alice bob (lift $ relabel aliceBid)
    bbid_rcvd <- runIFC $ bad_receive bob alice (lift $ bobAttackBid)
    abid_open <- runIFC $ bad_open alice bob (lift abid_rcvd)
    bbid_open <- runIFC $ bad_open bob alice (lift bbid_rcvd)
    let winner = bind abid_open $ \abid ->
                 bind bbid_open $ \bbid ->
                 if abid > bbid then
                   label "Alice wins" :: Lbl (Alice ∧ Bob) String
                 else if abid < bbid then
                   label "Bob wins"
                 else 
                   label "Tie" in
      runIFC $ do ebind winner $ \win ->
                   hPutStrLn @_ @_ @(Alice ∧ Bob) output win
  where 
   pcb = (((alice *∧ bob)*←) *∧ ((alice *∧ bob)*→))
   output = mkStdout pcb 
   (>>=)  = (P.>>=)
   bobAttack :: IFC IO (I Bob ∧ C Alice) (Bob ∧ C Alice) Int
   bobAttack = assume ((alice*←) ≽ (bob*←)) $
     ebind aliceBid $ \abid -> protect $ abid + 1

nmAuction :: IO (Lbl SU ())
nmAuction =
  do
    abid_rcvd <- runIFC $ runClr $ nm_receive alice bob (lift_b aliceBid)
    bbid_rcvd <- runIFC $ runClr $ nm_receive bob alice (lift_b bobBid)
    abid_open <- runIFC $ runClr $ nm_open alice bob (lift_b abid_rcvd)
    bbid_open <- runIFC $ runClr $ nm_open bob alice (lift_b bbid_rcvd)
    let winner = bind abid_open $ \abid ->
                 bind bbid_open $ \bbid ->
                 if abid > bbid then
                   (label "Alice wins"  :: Lbl (I (Alice ∧ Bob) ∧ C (Alice ∨ Bob)) String) 
                 else if abid < bbid then
                   label "Bob wins" 
                 else 
                   label "Tie" in
     runIFC $ runClr $ ebind_b winner $ \win -> 
                         hPutStrLn_b @ClrT @CtlT @Lbl
                                        @(I (Alice ∧ Bob) ∧ C (Alice ∨ Bob))
                                        @(I (Alice ∧ Bob) ∧ C (Alice ∨ Bob))
                                        @(I (Alice ∧ Bob) ∧ C (Alice ∨ Bob))
                                        output win
  where 
   pcb = (((alice *∧ bob)*←) *∧ ((alice *∨ bob)*→))
   output = mkStdout pcb
   (>>=)  = (P.>>=)

main = do
     flacAuction;
     badflacAuction;
     nmAuction
 where
   (>>)  = (P.>>)
