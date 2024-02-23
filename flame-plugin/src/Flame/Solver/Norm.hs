{-# LANGUAGE CPP #-}
module Flame.Solver.Norm where

import Flame.Solver.Data  
-- External
import Data.Either   (partitionEithers)
import Data.List     (sort, union, nub)
import Data.Graph    (graphFromEdges, reachable, vertices)
import Data.Function (on)
import Data.Map.Strict (findWithDefault)

-- GHC API
import GHC.Plugins
import GHC.Core.TyCo.Rep
import GHC.Tc.Utils.TcType
import GHC.Tc.Solver.Monad ( TcLevel )
import GHC.Driver.Session

-- import Type       (coreView, mkTyVarTy, mkTyConApp, expandTypeSynonyms)
-- import TcType     (TcLevel, isTouchableMetaTyVar)
-- import DynFlags

-- #if __GLASGOW_HASKELL__ >= 711
-- import TyCoRep    (Type (..), TyLit (..), UnivCoProvenance(..), Coercion(..))
-- #else
-- import TypeRep    (Type (..), TyLit (..))
-- #endif

mergeWith :: (a -> a -> Either a a) -> [a] -> [a]
mergeWith _ []      = []
mergeWith op (f:fs) = case partitionEithers $ map (`op` f) fs of
                        ([],_)              -> f : mergeWith op fs
                        (updated,untouched) -> mergeWith op (updated ++ untouched)

-- | Merge two symbols of a Meet term
--
-- Performs the following rewrites:
--
-- @
-- ⊤ ∨ x    ==>  x
-- x ∨ ⊤    ==>  x
-- x ∨ ⊥    ==>  0
-- ⊥ ∨ x    ==>  0
-- x ∨ x    ==>  x
-- @
mergeB :: (Eq v, Eq c) => Base v c -> Base v c
       -> Either (Base v c) (Base v c)
mergeB T r = Left r       -- ⊤ ∨ x ==> x
mergeB l T = Left l       -- x ∨ ⊤ ==> x
mergeB B _ = Left B       -- ⊥ ∨ x ==> ⊥
mergeB _ B = Left B       -- x ∨ ⊥ ==> ⊥
mergeB l r                -- y ∨ y ==> y
  | l == r = Left l
mergeB l _ = Right l

-- | Merge two components of a Join term
--
-- Performs the following rewrites:
--
-- @
-- ⊤ ∧ x       ==>  ⊤ 
-- x ∧ ⊤       ==>  ⊤
-- ⊥ ∧ x       ==>  x
-- x ∧ ⊥       ==>  x
-- x ∧ (x ∨ y) ==>  x  (Absorbtion)
-- (x ∨ y) ∧ x ==>  x  (Absorbtion)
-- @
mergeM :: (Eq v, Eq c) => MNorm v c -> MNorm v c
       -> Either (MNorm v c) (MNorm v c)
mergeM (M [T]) _ = Left (M [T])                   -- ⊤ ∧ x       ==>  ⊤ 
mergeM _ (M [T]) = Left (M [T])                   -- x ∧ ⊤       ==>  ⊤ 
mergeM (M (B:_)) r = Left r                       -- ⊥ ∧ x       ==>  x 
mergeM l (M (B:_)) = Left l                       -- x ∧ ⊥       ==>  x
mergeM (M [l]) (M rs) | elem l rs = Left (M [l])  -- x ∧ (x ∨ y) ==>  x
mergeM (M ls) (M [r]) | elem r ls = Left (M [r])  -- (x ∨ y) ∧ x  ==>  x
mergeM l r | l == r = Left l                      -- y ∧ y    ==>  y
mergeM l _ = Right l

zeroM :: MNorm v c -> Bool
zeroM (M (B:_)) = True
zeroM _         = False

mkNonEmpty :: JNorm v c -> JNorm v c
mkNonEmpty (J []) = J [M [B]]
mkNonEmpty s      = s

-- | Simplifies SOP terms using
--
-- * 'mergeM'
-- * 'mergeB'
simplifyJNorm :: (Ord v, Ord c) => JNorm v c -> JNorm v c
simplifyJNorm = mkNonEmpty
       . J
       . sort . filter (not . zeroM)
       . mergeWith mergeM
       . map (M . sort . mergeWith mergeB . unM)
       . unJ
{-# INLINEABLE simplifyJNorm #-}

-- | Merge two JNorm terms by join
mergeJNormJoin :: (Ord v, Ord c) => JNorm v c -> JNorm v c -> JNorm v c
mergeJNormJoin (J ms1) (J ms2) = simplifyJNorm $ J (ms1 ++ ms2)
{-# INLINEABLE mergeJNormJoin #-}

-- | Merge two JNorm terms by meet
mergeJNormMeet :: (Ord v, Ord c) => JNorm v c -> JNorm v c -> JNorm v c
mergeJNormMeet (J ms1) (J ms2)
  = simplifyJNorm
  . J
  $ concatMap (zipWith (\p1 p2 -> M (unM p1 ++ unM p2)) ms1 . repeat) ms2
{-# INLINEABLE mergeJNormMeet #-}

-- | Merge two Norm terms by join
mergeNormJoin :: (Ord v, Ord c) => Norm v c -> Norm v c -> Norm v c
mergeNormJoin (N c1 i1) (N c2 i2) = N (mergeJNormJoin c1 c2) (mergeJNormJoin i1 i2)
{-# INLINEABLE mergeNormJoin #-}

-- | Merge two Norm terms by meet
mergeNormMeet :: (Ord v, Ord c) => Norm v c -> Norm v c -> Norm v c
mergeNormMeet (N c1 i1) (N c2 i2) = N (mergeJNormMeet c1 c2) (mergeJNormMeet i1 i2)
{-# INLINEABLE mergeNormMeet #-}
 
-- | Convert a type of /kind/ 'Flame.Principals.KPrin' to a 'JNorm' term
-- flrec contains the KPrin type constructors
-- isConf indicates whether we are normalizing the conf component
jnormPrin :: FlameRec -> Bool -> Type -> Maybe CoreJNorm
jnormPrin flrec isConf ty | Just ty1 <- coreView ty = jnormPrin' ty1
  where jnormPrin' = jnormPrin flrec isConf
jnormPrin flrec isConf (TyVarTy v) = return $ J [M [V v]]
jnormPrin flrec isConf (TyConApp tc [])
  | tc == (ktop flrec) = return $ J [M [T]]
  | tc == (kbot flrec) = return $ J [M [B]]
jnormPrin flrec isConf (TyConApp tc [x])
  | tc == (kname flrec) = return $ J [M [P x]]
  | tc == (kconf flrec) =
    if isConf then jnormPrin' x else return $ J [M [B]]
  | tc == (kinteg flrec) = 
    if isConf then return $ J [M [B]] else jnormPrin' x
  | tc == (kvoice flrec) =
    if isConf then return $ J [M [B]] else integ <$> voiceOf <$> (normPrin flrec x)
  | tc == (keye flrec) =
    if isConf then conf <$> eyeOf <$> (normPrin flrec x) else return $ J [M [B]]
  where jnormPrin' = jnormPrin flrec isConf
jnormPrin flrec isConf (TyConApp tc [x,y])
  | tc == (kconj flrec) = mergeJNormJoin <$> jnormPrin' x <*> jnormPrin' y
  | tc == (kdisj flrec) = mergeJNormMeet <$> jnormPrin' x <*> jnormPrin' y
  where jnormPrin' = jnormPrin flrec isConf
jnormPrin flrec isConf ty = -- pprTrace "unexpected principal: " (ppr ty) $
                     return $ (J [M [U ty]])

---- | Convert a type of /kind/ 'Flame.Principals.KPrin' to a 'JNorm' term
normPrin :: FlameRec -> Type -> Maybe CoreNorm
normPrin flrec ty
  | Just ty1 <- coreView ty = normPrin flrec ty1
normPrin flrec (TyVarTy v) = return $ N (J [M [V v]]) (J [M [V v]])
normPrin flrec (TyConApp tc [])
  | tc == (ktop flrec) = return $ N (J [M [T]]) (J [M [T]])
  | tc == (kbot flrec) = return $ N (J [M [B]]) (J [M [B]])
normPrin flrec (TyConApp tc [x])
  | tc == (kname flrec)  = return $ N (J [M [P x]]) (J [M [P x]])
  | tc == (kconf flrec)  = N <$> (jnormPrin flrec True x) <*> (Just (J [M [B]]))
  | tc == (kinteg flrec) = N (J [M [B]]) <$> (jnormPrin flrec False x)
  | tc == (kvoice flrec) = voiceOf <$> normPrin flrec x
  | tc == (keye flrec)   = eyeOf <$> normPrin flrec x
normPrin flrec (TyConApp tc [x,y])
  | tc == (kconj flrec) = mergeNormJoin <$> normPrin flrec x <*> normPrin flrec y 
  | tc == (kdisj flrec) = mergeNormMeet <$> normPrin flrec x <*> normPrin flrec y 
normPrin flrec ty = -- pprTrace "unexpected principal: " (ppr ty) $
                     return $ N (J [M [U ty]]) (J [M [U ty]])
  
voiceOf :: Norm v s -> Norm v s
voiceOf (N conf _) = N (J [M [B]]) (wrapVars conf)
  where
    wrapVars (J ms) = J (map wrapVars' ms)
    wrapVars' (M bs) = M (map wrapVars'' bs)
    wrapVars'' (V v) = VarVoice v 
    wrapVars'' (VarVoice v) = VarVoice v 
    wrapVars'' (VarEye v) = (V v)
    wrapVars'' (UVoice s) = UVoice s
    wrapVars'' (UEye   s) = (U s)
    wrapVars'' p = p
  
eyeOf :: Norm v s -> Norm v s
eyeOf (N _ integ) = N (wrapVars integ) (J [M [B]]) 
  where
    wrapVars (J ms) = J (map wrapVars' ms)
    wrapVars' (M bs) = M (map wrapVars'' bs)
    wrapVars'' (V v) = VarEye v 
    wrapVars'' (VarVoice v) = (V v) 
    wrapVars'' (VarEye v) = VarEye v 
    wrapVars'' (UVoice s) = U s
    wrapVars'' (UEye   s) = UEye s
    wrapVars'' p = p

-- | Convert a 'SOP' term back to a type of /kind/ 'GHC.TypeLits.Nat'
reifyNorm :: FlameRec -> CoreNorm -> Type
reifyNorm flrec (N cp ip) =
  let c' = reifyJNorm flrec cp in
  let i' = reifyJNorm flrec ip in
    mkTyConApp (kconj flrec)
      [mkTyConApp (kconf flrec) [c'],
       mkTyConApp (kinteg flrec) [i']]
  where

reifyJNorm :: FlameRec -> CoreJNorm -> Type
reifyJNorm flrec (J [])     = mkTyConApp (kbot flrec) []
reifyJNorm flrec (J [p])    = reifyMNorm flrec p
reifyJNorm flrec (J (p:ps)) = let es = reifyJNorm flrec (J ps)
                              in mkTyConApp (kconj flrec) [reifyMNorm flrec p, es]

reifyMNorm :: FlameRec -> CoreMNorm -> Type
reifyMNorm flrec = foldr1 (\t1 t2 -> mkTyConApp (kdisj flrec) [t1,t2])
             . map (reifyBase flrec) . unM

reifyBase :: FlameRec -> CoreBase -> Type
reifyBase flrec (V v)   = mkTyVarTy v
reifyBase flrec (VarEye v)   = mkTyConApp (keye flrec) [mkTyVarTy v]
reifyBase flrec (VarVoice v) = mkTyConApp (kvoice flrec) [mkTyVarTy v]
reifyBase flrec (U s)   = s
reifyBase flrec (UEye s)   = mkTyConApp (keye flrec) [s]
reifyBase flrec (UVoice s) = mkTyConApp (kvoice flrec) [s]
reifyBase flrec (P s)   = mkTyConApp (kname flrec) [s]
reifyBase flrec B       = mkTyConApp (kbot flrec) []
reifyBase flrec T       = mkTyConApp (ktop flrec) []


cartProd :: JNorm v s -> [JNorm v s]
cartProd (J ms) = [J $ map mkM ps | ps <- sequence [bs | (M bs) <- ms]]
  where mkM p = M [p]

flattenDelegations :: [(Norm v s, Norm v s)]
                   -> ([(JNorm v s, JNorm v s)], [(JNorm v s, JNorm v s)])
flattenDelegations givens = foldl
                      (\(cacc, iacc) given ->
                        case given of
                          -- convert to "base form"
                          -- base form is:
                          --  (b ∧ b ...) ≽ (b ∨ b ...)
                          --   joins of base principals on LHS
                          --   meets of base principals on RHS
                          (N supJC supJI, N (J infMCs) (J infMIs)) -> 
                            ([(supC, J [infC]) | supC <- cartProd supJC, infC <- infMCs] ++ cacc,
                             [(supI, (J [infI])) | supI <- cartProd supJI, infI <- infMIs] ++ iacc)
                      )
                      ([] :: [(JNorm v s, JNorm v s)], [] :: [(JNorm v s, JNorm v s)])
                      givens
  where
    cartProd (J ms) = [J $ map mkM ps | ps <- sequence [bs | (M bs) <- ms]]
    mkM p = M [p]

 {- 
   TODO: delegations based on structural edges
   - for each conjunction on the LHS, add a pseudo-node to the graph that is
       reachable from each conjunct and from which the intersection of the
       superiors of each conjunct are reachable.
   - for each disjunction on the RHS, add a pseudo-node to the graph that
       reaches the disjunction and is reachable from the intersection of
       the inferiors of each disjunct.
   - compute fixpoint
 -}
computeDelClosure :: [(CoreJNorm,CoreJNorm)] -> CoreDelClosure
computeDelClosure givens = -- pprTrace "computing closure from" (ppr givens) $
  [(inferior, superiors) | (inferior, _, superiors) <- fixpoint initialEdges]
  where
    top = (J [M [T]])
    bot = (J [M [B]])
    baseSeqToJ seq = J [M seq]
    
    structJoinEdges :: CoreJNorm -> [(CoreJNorm, CoreJNorm, [CoreJNorm])]
    structJoinEdges (J []) = [] 
    structJoinEdges (J seq) = 
      {- for sequence of elements in each conjunct, add an edge from that sequence to the conjunct -}
      [(J inf, J inf, [J seq]) | inf <- subsequencesOfSize (length seq - 1) seq]
      {- recurse on all subsequences -}
      ++ concat [structJoinEdges (J inf) | inf <- subsequencesOfSize (length seq - 1) seq]

    structMeetEdges :: CoreJNorm -> [(CoreJNorm, CoreJNorm, [CoreJNorm])]
    structMeetEdges (J [M []]) = [] 
    structMeetEdges (J [M seq]) = 
      {- for each disjunct, add an edge to each subsequence of the disjunct -}
      [(baseSeqToJ seq, baseSeqToJ seq, map baseSeqToJ $ subsequencesOfSize (length seq - 1) seq)]
      ++ concat [structMeetEdges (J [M sup]) | sup <- subsequencesOfSize (length seq - 1) seq]
    {- for principals in base form, there are no other structural meet edges -}
    structMeetEdges (J seq) = []

    initialEdges :: [(CoreJNorm, CoreJNorm, [CoreJNorm])]
    initialEdges = [(inf, inf, sort $ union (union (nub [gsup | (gsup, ginf) <- givens, ginf == inf])
                                            $ concat [jsups | (jinf, _, jsups) <- structJoinEdges inf, jinf == inf])
                                     $ (concat [msups | (minf, _, msups) <- structMeetEdges inf, minf == inf] ++ [top])
                                     )
                    | inf <- principals]

    {-
      For principals in a given in base form, 
        (b ∧ b ...) ≽ (b ∨ b ...)
      we want a node for each subsequence of conjuncts and disjuncts
    -}
    principals :: [CoreJNorm]
    principals = [top, bot] ++ (nub $ concat [(map J $ concat [subsequencesOfSize i psC | i <- [1..length psC]]) ++
                                              (map baseSeqToJ $ concat [subsequencesOfSize i qs | i <- [1..length qs]])
                                             | (J psC, J [M qs]) <- givens])
    -- http://stackoverflow.com/questions/21265454/subsequences-of-length-n-from-list-performance
    subsequencesOfSize :: Int -> [a] -> [[a]]
    subsequencesOfSize n xs = let l = length xs
                              in if n>l then [] else subsequencesBySize xs !! (l-n)
    subsequencesBySize [] = [[[]]]
    subsequencesBySize (x:xs) = let next = subsequencesBySize xs
                              in zipWith (++) ([]:next) (map (map (x:)) next ++ [[]])

    fixpoint edges = let (graph, vtxToEdges, prinToVtx) = graphFromEdges edges in
                     let vtxToPrin v = let (x, _, _) = vtxToEdges v in x in
                     let newEdges = [(vtxToPrin inf, vtxToPrin inf, 
                                                        (sort (map vtxToPrin $ reachable graph inf)) ++
                                                        computeStructEdges (graph, vtxToEdges, prinToVtx) inf)
                                    | inf <- vertices graph] in
                     if edges == newEdges then
                       newEdges 
                     else 
                       fixpoint newEdges

    -- TODO: implement
    computeStructEdges (graph, vtxToEdges, prinToVtx) vtx = []

substJNorm :: TcLevel -> CoreBounds -> Bool -> CoreJNorm -> CoreJNorm
substJNorm level bounds isConf = foldr1 mergeJNormJoin . map (substMNorm level bounds isConf) . unJ

substMNorm :: TcLevel -> CoreBounds -> Bool -> CoreMNorm -> CoreJNorm
substMNorm level bounds isConf = foldr1 mergeJNormMeet . map (substBase level bounds isConf) . unM

substBase :: TcLevel -> CoreBounds -> Bool -> CoreBase -> CoreJNorm
substBase _ _ _ B = jbot
substBase _ _ _ T = J [M [T]]
substBase _ _ _ p@(P s) = J [M [p]]
substBase _ _ _ u@(U s) = J [M [u]]
substBase level bounds isConf (V tv) | isTouchableMetaTyVar level tv =
  let s = findWithDefault jbot tv bounds in
   {- pprTrace "subst " (ppr tv <+> ppr s) $-} s
substBase level bounds isConf (V tv) = J [M [V tv]]
substBase level bounds isConf (VarVoice tv) | isTouchableMetaTyVar level tv = 
  if isConf then
    undefined -- XXX: should have already been removed
  else
    integ (voiceOf (N (findWithDefault jbot tv bounds) jbot))
substBase level bounds isConf (VarVoice tv) = J [M [VarVoice tv]]
substBase level bounds isConf (VarEye tv) | isTouchableMetaTyVar level tv = 
  if isConf then 
    conf (eyeOf (N jbot (findWithDefault jbot tv bounds)))
  else
    undefined -- XXX: should have already been removed
substBase level bounds isConf (VarEye tv) = J [M [VarEye tv]]
substBase level bounds isConf (UVoice t) = J [M [UVoice t]]
substBase level bounds isConf (UEye t) = J [M [UEye t]]

jbot = J [M [B]]

---- | Print a type of /kind/ 'Flame.Principals.KPrin' 
outputKPrin :: FlameRec -> Type -> String
outputKPrin flrec ty
  | Just ty1 <- coreView ty = outputKPrin flrec ty1
outputKPrin flrec (TyVarTy v) = showGhc v
outputKPrin flrec (TyConApp tc [])
  | tc == (ktop flrec) = "⊤"
  | tc == (kbot flrec) = "⊥"
outputKPrin flrec (TyConApp tc [x])
  | tc == (kname flrec)  = showGhc x
  | tc == (kconf flrec)  = (outputKPrin flrec x  ++ " →")
  | tc == (kinteg flrec) = (outputKPrin flrec x ++ " ←")
  | tc == (kvoice flrec) = ("∇(" ++ outputKPrin flrec x  ++ ")")
  | tc == (keye flrec)   = ("Δ(" ++ outputKPrin flrec x  ++ ")")
outputKPrin flrec (TyConApp tc [x,y])
  | tc == (kconj flrec) = ("(" ++ outputKPrin flrec x ++ " ∧ " ++ outputKPrin flrec y ++ ")")
  | tc == (kdisj flrec) = ("(" ++ outputKPrin flrec x ++ " ∨ " ++ outputKPrin flrec y ++ ")")
outputKPrin flrec ty    = showGhc ty

showGhc :: (Outputable a) => a -> String
showGhc = showPprUnsafe 
