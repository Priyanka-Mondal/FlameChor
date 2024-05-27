{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}
module ShouldSucceed where

import Flame.Principals
import Flame.Runtime.Principals
import Flame.IFC 

five :: FLA m e n => SPrin p 
       -> m e n (I p) (C p) a
       -> m e n (I p) p  a
five p v = assume (((SBot)*←) ≽ (p*←)) (reprotect v)

{- #5 not allowed.  This endorsement is malleable. -}
{-
nm_five :: BFLA m e n => SPrin p 
       -> c m e n (Δ KBot) (I p) (C p) a
       -> c m e n (Δ KBot) (I p) p  a
nm_five p v = iassume (((SBot)*←) ≽ (p*←)) (reprotect_b v)
-}
{- #5 Alternative 1: Commit only public data. committing it makes it secret. -}
nm_five' :: BFLA c m e n => SPrin p 
       -> c m e n (Δ KBot) (I p) KBot a
       -> c m e n (Δ KBot) (I p) p  a
nm_five' p v = iassume (((SBot)*←) ≽ (p*←)) (reprotect_b v)

{- #5 Alternative 2: with higher integrity pc, could declass, then endorse.
   seems a little weird, but this is what explicitly permitting malleability
   looks like, I suppose
NB: this doesn't work yet, but might with some extra reasoning in the solver
nm_five'' :: (BFLA c m e n, p ⊑ Δ p) => SPrin p 
       -> c m e n (Δ p ∧ C p) (I p ∧ ((∇) p)) (C p) a
       -> c m e n (Δ p ∧ C p) (I p ∧ ((∇) p)) p  a
nm_five'' p v = vassume ((*∇)(SBot*→) ≽ (*∇)(p*→)) $
                 eassume (SEye SBot ≽ SEye p) $
                  cassume ((SBot*→) ≽ (p*→)) $
                   iassume ((SBot*←) ≽ (p*←)) $ (reprotect_b v)
-}
