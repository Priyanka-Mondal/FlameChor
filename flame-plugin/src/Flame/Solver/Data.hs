{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Flame.Solver.Data where
-- External
import Data.IORef (IORef)
import Data.Map.Strict (Map, union, keys, fromList)

-- GHC API
import GHC.Plugins (Type, TyCon, TyVar, ($$), (<+>), text, Outputable(..), ppr, hcat, punctuate, eqType, nonDetCmpType)
import GHC.Tc.Types.Constraint ( Ct )
import GHC.Tc.Types.Evidence ( EvTerm, EvExpr )
import GHC.Tc.Solver.Monad ( TcLevel )




-- import TyCon      (TyCon)
-- import Outputable (Outputable (..), (<+>), text, hcat, punctuate, ppr, ($$))
-- import Type       (Type,TyVar)
-- import TcRnTypes  (Ct)
-- import TcEvidence (EvTerm (..))
-- import TcType     (TcLevel)
-- 
-- #if 904 >= 711
-- import Type       (eqType)
-- #endif
-- #if 904 < 82
-- import Type       (cmpType)
-- #else
-- import Type       (nonDetCmpType)
-- #endif

instance Eq Type where
  (==) = eqType

instance Ord Type where
  compare = nonDetCmpType

data Base v s
  = P s -- ^ Primitive principal
  | U s -- ^ Uninterpreted type
  | V v -- ^ Type var
  | B   -- ^ Bottom
  | T   -- ^ Top
  | VarVoice v -- ^ Voice of type var
  | VarEye v -- ^ Eye of type var
  | UVoice s -- ^ Voice of uninterpreted type
  | UEye   s -- ^ Eye of uninterpreted type
  deriving (Eq,Ord)

newtype MNorm v s = M { unM :: [Base v s]}
  deriving (Eq)

instance (Ord v, Ord c) => Ord (MNorm v c) where
  compare (M [x])   (M [y])   = compare x y
  compare (M [_])   (M (_:_)) = LT
  compare (M (_:_)) (M [_])   = GT
  compare (M xs)    (M ys)    = compare xs ys

newtype JNorm v s = J { unJ :: [MNorm v s]}
  deriving (Ord)

instance (Eq v, Eq s) => Eq (JNorm v s) where
  (J []) == (J [M [B]]) = True
  (J [M [B]]) == (J []) = True
  (J ms1) == (J ms2) = ms1 == ms2

data Norm v s = N {conf :: JNorm v s, integ :: JNorm v s}
  deriving (Ord)

instance (Eq v, Eq s) => Eq (Norm v s) where
  N c1 i1 == N c2 i2 = c1 == c2 && i1 == i2

instance (Outputable v, Outputable s)  => Outputable (Norm v s) where
  ppr (N c i) = case (pprSimple c, pprSimple i) of
                  (cS, iS) -> cS <+> text "→ ∧ " <+> iS <+> text "←"
    where
      pprSimple (J [M [P s]]) = ppr s
      pprSimple (J [M [U s]]) = ppr s
      pprSimple (J [M [V v]]) = ppr v
      pprSimple (J [M [B]]) = text "⊥"
      pprSimple (J [M [T]]) = text "⊤"
      pprSimple sop           = text "(" <+> ppr sop <+> text ")"

instance (Outputable v, Outputable s) => Outputable (JNorm v s) where
  ppr = hcat . punctuate (text " ∧ ") . map ppr . unJ

instance (Outputable v, Outputable s) => Outputable (MNorm v s) where
  ppr s = text "(" <+> (hcat . punctuate (text " ∨ ") . map ppr . unM) s <+> text ")"

instance (Outputable v, Outputable s) => Outputable (Base v s) where
    ppr (P s)   = ppr s
    ppr (V s)   = ppr s
    ppr (U s)   = ppr s
    ppr B = text "⊥"
    ppr T = text "⊤"
    ppr (VarVoice v) = text "∇(" <+> ppr v <+> text "→)"
    ppr (VarEye v) = text "Δ(" <+> ppr v <+> text "→)"
    ppr (UVoice v) = text "∇(" <+> ppr v <+> text "→)"
    ppr (UEye v) = text "Δ(" <+> ppr v <+> text "→)"

-- | 'Norm' with 'TyVar' variables
type CoreNorm       = Norm TyVar  Type
type CoreJNorm      = JNorm TyVar Type
type CoreMNorm      = MNorm TyVar Type
type CoreBase       = Base TyVar  Type


type DelClosure v s = [(JNorm v s, [JNorm v s])]
type CoreDelClosure = DelClosure TyVar  Type

type Bounds v s = Map v (JNorm v s)
type CoreBounds = Bounds TyVar Type

data FlameRec = FlameRec {
   kprin        :: TyCon,
   ktop         :: TyCon,
   kbot         :: TyCon,
   kname        :: TyCon,
   kconj        :: TyCon,
   kdisj        :: TyCon,
   kconf        :: TyCon,
   kinteg       :: TyCon,
   kvoice       :: TyCon,
   keye         :: TyCon,
   actsfor      :: TyCon,
   confClosure  :: CoreDelClosure,
   integClosure :: CoreDelClosure,
   confBounds   :: CoreBounds,
   integBounds  :: CoreBounds,
   tclevel      :: TcLevel
 }

getBounds :: FlameRec -> Bool -> CoreBounds
getBounds flrec isConf =
  if isConf then
    confBounds flrec
  else
    integBounds flrec

updateBounds :: FlameRec -> Bool -> [(TyVar, JNorm TyVar Type)] -> FlameRec
updateBounds flrec isConf newBnds =
 if isConf then
   flrec{confBounds = fromList newBnds `union` getBounds flrec isConf}
 else
   flrec{integBounds = fromList newBnds `union` getBounds flrec isConf}

data SimplifyResult
  = Simplified ([(EvTerm,Ct)],[Ct])
  | Impossible ActsForCt

instance Outputable SimplifyResult where
  ppr (Simplified evs) = text "Simplified" $$ ppr evs
  ppr (Impossible eq)  = text "Impossible" <+> ppr eq

data SolverResult
  = Win                      -- ^ Two terms are equal
  | Lose ActsForCt
  | ChangeBounds [(TyVar, CoreJNorm)] -- ^ Two terms are only equal if the given substitution holds

resultBounds :: SolverResult -> [(TyVar, CoreJNorm)]
resultBounds result =
  case result of
    ChangeBounds bnds -> bnds
    Win -> []
    Lose af -> error "should not happen"

changedVars :: SolverResult -> [TyVar]
changedVars result =
  case result of
    ChangeBounds bnds -> keys $ fromList bnds
    Win -> []
    Lose af -> error "should not happen"

instance Outputable SolverResult where
  ppr Win          = text "Win"
  ppr (ChangeBounds bnds) = text "ChangeBounds" <+> ppr bnds
  ppr (Lose af)       = text "Lose"

type ActsForCt = (Ct, (CoreNorm, CoreNorm))

fromActsFor :: ActsForCt -> Ct
fromActsFor (ct, _)    = ct


