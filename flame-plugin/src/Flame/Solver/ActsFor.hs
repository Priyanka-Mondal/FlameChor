{-# LANGUAGE CPP #-}
module Flame.Solver.ActsFor
       ( ActsForProof(..)
       , actsFor
       , actsForJ
       )
where

import Flame.Solver.Data  
import Flame.Solver.Norm

-- External
import Data.Maybe  (mapMaybe)
import Data.List   (find)

-- GHC API
--import Outputable (Outputable (..), (<+>), text, ppr)
import GHC.Plugins

data ActsForProof =                    
      AFTop
    | AFBot
    | AFRefl 
    | AFDel (CoreBase, CoreBase) -- NB: this implicitly uses transitivity on given dels
    | AFConj [ActsForProof] -- for each RHS q, proof that there is a LHS p s.t. p > q 
    | AFDisj [ActsForProof] -- for each RHS q, proof that there is a LHS p s.t. p > q 

instance Outputable ActsForProof where
    ppr AFTop = text "AFTop"
    ppr AFBot = text "AFBot"
    ppr AFRefl = text "AFRefl"
    ppr (AFDel del) = text "AFDel" <+> ppr del
    ppr (AFConj pfs) = text "AFConj" <+> ppr pfs
    ppr (AFDisj pfs) = text "AFDisj" <+> ppr pfs

-- TODO: treat uninstantiated vars as bottom
actsFor :: FlameRec -> CoreNorm -> CoreNorm -> Maybe ActsForProof
actsFor flrec p q 
  | p == top = Just AFTop
  | q == bot = Just AFBot
  | p == q   = Just AFRefl
  | otherwise = do
          confPf <- actsForJ flrec True (conf p) (conf q)
          integPf <- actsForJ flrec False (integ p) (integ q)
          Just $ AFConj [confPf, integPf]
  where
    top :: CoreNorm
    top = N (J [M [T]]) (J [M [T]])
    bot :: CoreNorm
    bot = N (J [M [B]]) (J [M [B]])
    --confActsFor :: CoreJNorm -> CoreJNorm -> Maybe ActsForProof
    --confActsFor = actsForJ (confClosure flrec)
    --integActsFor :: CoreJNorm -> CoreJNorm -> Maybe ActsForProof
    --integActsFor = actsForJ (integClosure flrec)

actsForJ :: FlameRec -> Bool -> CoreJNorm -> CoreJNorm -> Maybe ActsForProof
actsForJ flrec isConf p q 
  | p == top  = Just AFTop
  | q == bot  = Just AFBot
  | p == q    = Just AFRefl
  | otherwise = AFConj <$> conjProofs 
  where
    top :: CoreJNorm
    top = J [M [T]]
    bot :: CoreJNorm
    bot = J [M [B]] 
    -- for every join comp on rhs, find sup on lhs
    (J pms, J qms) = (p,q)
    conjProofs :: Maybe [ActsForProof]
    conjProofs = sequence $ map (\qm ->
                                  case mapMaybe
                                         (\pm -> actsForM flrec isConf pm qm)
                                         pms
                                  of
                                    (pf:pfs) ->
                                      Just pf
                                    [] -> Nothing
                                )
                                qms

actsForM :: FlameRec -> Bool -> CoreMNorm -> CoreMNorm ->
            Maybe ActsForProof
actsForM flrec isConf p q
  | p == top  = Just AFTop
  | q == bot  = Just AFBot
  | p == q    = Just AFRefl
  | otherwise = AFDisj <$> disjProofs
  where
    top :: CoreMNorm
    top = M [T]
    bot :: CoreMNorm
    bot = M [B] 
    -- for every meet comp on lhs, find inf on rhs
    (M pbs, M qbs) = (p,q)
    disjProofs :: Maybe [ActsForProof]
    disjProofs = sequence $ map (\pb ->
                                  case mapMaybe (\qb ->
                                                  actsForB flrec isConf pb qb)
                                                qbs
                                  of
                                    (pf:pfs) -> Just pf
                                    [] -> Nothing
                                )
                                pbs
-- IDEA for transitivity.  If all given dels are expressed "primitively",
-- then transitivity can be exploited as simple reachability via given dels.
actsForB :: FlameRec -> Bool -> CoreBase -> CoreBase ->
            Maybe ActsForProof
actsForB flrec isConf _p _q 
  | p == top = Just AFTop
  | q == bot = Just AFBot
  | p == q  = Just AFRefl
  | otherwise = 
    case find (== p) (superiors q) of
      Just del -> Just $ AFDel (_p,_q) -- TODO: encode bounds in proof
      _ -> Nothing
  where
    p = J [M [_p]]
    q = J [M [_q]]
    top :: CoreJNorm
    top = J [M [T]]
    bot :: CoreJNorm
    bot = J [M [B]]  
    bounds = if isConf then confBounds flrec else integBounds flrec
    --      XXX : what about structural superiors!?
    --      might need to iterate on fixpoint here again
    delClosure = if isConf then confClosure flrec else integClosure flrec
    superiors :: CoreJNorm -> [CoreJNorm]
    superiors q = case find ((== q) . fst) delClosure of
                    Just (q, sups) -> map (substJNorm (tclevel flrec) bounds isConf) sups
                    _ | q /= top -> superiors top
                    _ -> []
