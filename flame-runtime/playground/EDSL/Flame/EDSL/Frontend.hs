{-# LANGUAGE CPP #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin Flame.Solver #-}


-- Front end for imperative programs

module Flame.EDSL.Frontend where

import Prelude hiding (break)
import Flame.Principals
import Flame.EDSL.IFC
import Flame.EDSL.Do

import Data.Array.IO
import Data.IORef
import Data.Typeable
import System.IO.Unsafe
import qualified System.IO as IO (Handle) 
import System.IO as IO (IOMode) 

import Control.Monad.Operational.Higher
import System.IO.Fake
import Language.Embedded.Expression
import Language.Embedded.Imperative.CMD hiding (stdin, stdout, Handle, Ref)
import qualified Language.Embedded.Imperative.CMD as CMD (Handle, Ref)


--------------------------------------------------------------------------------
-- * References
--------------------------------------------------------------------------------
newtype Ref (l::KPrin) a = LABRef { unRef :: CMD.Ref a}

-- | Create an uninitialized reference
newRef :: (pred a, pc ⊑ l, RefCMD :<: instr) =>
    LABProgram exp instr pred pc pc (Ref l a)
newRef = newNamedRef "r"

-- | Create an uninitialized named reference
--
-- The provided base name may be appended with a unique identifier to avoid name
-- collisions.
newNamedRef :: (pred a, pc ⊑ l, RefCMD :<: instr)
    => String  -- ^ Base name
    -> LABProgram exp instr pred pc pc (Ref l a)
newNamedRef s = LAB $ LABRef <$> (singleInj $ NewRef s)

-- | Create an initialized reference
initRef :: (pred a, pc ⊑ l, RefCMD :<: instr)
    => exp a  -- ^ Initial value
    -> LABProgram exp instr pred pc pc (Ref l a)
initRef = initNamedRef "r"

-- | Create an initialized named reference
--
-- The provided base name may be appended with a unique identifier to avoid name
-- collisions.
initNamedRef :: (pred a, pc ⊑ l, RefCMD :<: instr)
    => String  -- ^ Base name
    -> exp a   -- ^ Initial value
    -> LABProgram exp instr pred pc pc (Ref l a)
initNamedRef base a = LAB $ LABRef <$> (singleInj (InitRef base a))

-- | Get the contents of a reference
getRef :: (pred a, FreeExp exp, FreePred exp a, RefCMD :<: instr) =>
    Ref l a -> LABProgram exp instr pred pc (pc ⊔ l) (exp a) 
getRef = LAB. fmap valToExp . singleInj . GetRef . unRef

-- | Set the contents of a reference
setRef :: (pred a, pc ⊑ l, RefCMD :<: instr) =>
    Ref l a -> exp a -> LABProgram exp instr pred pc l' ()
setRef r = LAB . singleInj . SetRef (unRef r)

-- | Modify the contents of reference
modifyRef :: forall exp instr pred pc l l' a.
          (pred a, pc ⊑ l, l ⊑ pc, FreeExp exp, FreePred exp a, RefCMD :<: instr) =>
          Ref l a -> (exp a -> exp a) -> LABProgram exp instr pred pc (l::KPrin) ()
modifyRef r f = use (ifmap f (unsafeFreezeRef r) :: LABProgram exp instr pred pc (pc ⊔ l) (exp a)) $ \v ->
                setRef @_ @_ @pc r v

-- | Freeze the contents of reference (only safe if the reference is not updated
-- as long as the resulting value is alive)
unsafeFreezeRef
    :: (pred a, l ⊑ pc, FreeExp exp, FreePred exp a, RefCMD :<: instr)
    => Ref l a -> LABProgram exp instr pred pc (pc ⊔ l) (exp a)
unsafeFreezeRef = LAB . fmap valToExp . singleInj . UnsafeFreezeRef . unRef

--------------------------------------------------------------------------------
-- * Arrays
--------------------------------------------------------------------------------
-- TODO 
--------------------------------------------------------------------------------
-- * Control flow
--------------------------------------------------------------------------------
-- | Conditional statement
iff :: (ControlCMD :<: instr)
    => exp Bool      -- ^ Condition
    -> LABProgram exp instr pred pc l () -- ^ True branch
    -> LABProgram exp instr pred pc l () -- ^ False branch
    -> LABProgram exp instr pred pc l () -- ^ False branch
iff b (LAB t) (LAB f) = LAB $ singleInj $ If b t f

-- | Conditional statement that returns an expression
ifE :: forall pred exp instr pc l a. ( pred a
       , FreeExp exp
       , FreePred exp a
       , ControlCMD :<: instr
       , RefCMD     :<: instr
       , pc ⊑ l
       )
    => exp Bool         -- ^ Condition
    -> LABProgram exp instr pred pc l (exp a) -- ^ True branch
    -> LABProgram exp instr pred pc l (exp a) -- ^ False branch
    -> LABProgram exp instr pred pc l (exp a)
ifE b t f =
    [flame| do
    (r :: Ref l a) <- newRef 
    iff b
        (use t $ setRef r)
        (use f $ setRef r) :: LABProgram exp instr pred pc l Unit
    reprotect $ getRef r
    |] 

type Unit = () -- Quasiquoter doesn't like () for some reason

-- | While loop
while :: (ControlCMD :<: instr)
    => LABProgram exp instr pred (pc ⊔ l) l (exp Bool) -- ^ condition
    -> LABProgram exp instr pred (pc ⊔ l) l' () -- ^ Loop body
    -> LABProgram exp instr pred pc l' ()
while (LAB b) (LAB t) = LAB $ singleInj $ While b t

{-
-- | For loop
for
    :: ( FreeExp exp
       , ControlCMD :<: instr
       , Integral n
       , pred n
       , FreePred exp n
       )
    => IxRange (exp n)                                   -- ^ Index range
    -> (exp n -> ProgramT instr (Param3 exp pred pc) m ())  -- ^ Loop body
    -> ProgramT instr (Param3 exp pred pc) m ()
for range body = singleInj $ For range (body . valToExp)

-- | Break out from a loop
break :: (ControlCMD :<: instr) => ProgramT instr (Param3 exp pred pc) m ()
break = singleInj Break

-- | Assertion
assert :: (ControlCMD :<: instr)
    => exp Bool  -- ^ Expression that should be true
    -> String    -- ^ Message in case of failure
    -> ProgramT instr (Param3 exp pred pc) m ()
assert cond msg = singleInj $ Assert cond msg
-}


--------------------------------------------------------------------------------
-- * Pointer operations
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- * File handling
--------------------------------------------------------------------------------
-- | File handle
newtype Handle (l::KPrin) = LABHandle { unHandle :: CMD.Handle}

-- | Handle to stdin
stdin :: Handle KBot
stdin = LABHandle $ HandleComp "stdin"

-- | Handle to stdout
stdout :: Handle KBot
stdout = LABHandle $ HandleComp "stdout"

-- | Open a file
fopen :: forall pc l exp instr pred. (FileCMD :<: instr, pc ⊑ l) =>
     DPrin l -> FilePath -> IOMode -> LABProgram exp instr pred pc pc (Handle l)
-- TODO: must check whether l is correct label for file
-- l protects both the contents of the file + the status of the file handle (e.g., open/closed)
-- TODO: what is the fact that the file exists checked by?
fopen l file mode = LAB $ LABHandle <$> (singleInj $ FOpen file mode)

-- | Close a file
fclose :: (FileCMD :<: instr, pc ⊑ l) => Handle l -> LABProgram exp instr pred pc l' ()
fclose h = LAB $ singleInj $ FClose $ unHandle h

-- | Check for end of file
feof :: (FreeExp exp, FreePred exp Bool, FileCMD :<: instr) =>
    Handle l -> LABProgram exp instr pred pc (pc ⊔ l) (exp Bool)
feof h = LAB $ do
  b <- singleInj $ FEof $ unHandle h
  return $ valToExp b

class PrintfType l r
  where
    type PrintfPC r :: KPrin
    type PrintfExp r :: * -> *
    fprf :: ((PrintfPC r) ⊑ l) => Handle l -> String -> [PrintfArg (PrintfExp r)] -> r

instance (FileCMD :<: instr, a ~ ()) => PrintfType l (LABProgram exp instr pred (pc :: KPrin) l' a)
  where
    type PrintfPC (LABProgram exp instr pred pc l' a) = pc
    type PrintfExp (LABProgram exp instr pred pc l' a) = exp
    fprf h form as = LAB $ singleInj $ FPrintf (unHandle h) form (reverse as)

instance (Formattable a, PrintfType l r, exp ~ PrintfExp r, pc ~ PrintfPC r) =>
    PrintfType l (exp a -> r)
  where
    type PrintfPC (exp a -> r) = PrintfPC r
    type PrintfExp (exp a -> r) = exp
    fprf h form as = \a -> fprf h form (PrintfArg a : as)

-- | Print to a handle. Accepts a variable number of arguments.
fprintf :: (PrintfType l r, (PrintfPC r) ⊑ l) => Handle l -> String -> r
fprintf h format = fprf h format []

-- | Put a single value to a handle
fput :: forall instr exp pred a m pc l
    .  (Formattable a, FreePred exp a, FileCMD :<: instr, pc ⊑ l)
    => Handle l
    -> String  -- ^ Prefix
    -> exp a   -- ^ Expression to print
    -> String  -- ^ Suffix
    -> LABProgram exp instr pred pc pc ()
fput hdl prefix a suffix =
    fprintf hdl (prefix ++ formatSpecPrint (Proxy :: Proxy a) ++ suffix) a

-- | Get a single value from a handle
fget
    :: ( Formattable a
       , pred a
       , FreeExp exp
       , FreePred exp a
       , FileCMD :<: instr
       , l ⊑ pc
       )
    => Handle l -> LABProgram exp instr pred pc (pc ⊔ l) (exp a)
fget h = LAB $ do
           v <- singleInj $ FGet $ unHandle h
           return $ valToExp v

-- | Print to @stdout@. Accepts a variable number of arguments.
printf :: (PrintfType KBot r, PrintfPC r ⊑ KBot) => String -> r
printf = fprintf stdout
{-
-}
