{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
-- | Kind/type inference/checking, mirroring Language.PlutusCore.TypeCheck
module Language.PlutusIR.TypeCheck
    (
    -- * Configuration.
      DynamicBuiltinNameTypes (..)
    , TypeCheckConfig (..)
    , tccDynamicBuiltinNameTypes
    , PLC.defConfig
    , PLC.dynamicBuiltinNameMeaningsToTypes
    -- * Type inference/checking, extending the plc typechecker
    , inferType
    , checkType
    , inferTypeOfProgram
    , checkTypeOfProgram
    -- * Kind inference/checking, taken directly from plc typechecker
    , PLC.inferKind
    , PLC.checkKind
    ) where

import           Language.PlutusCore.Quote
import           Language.PlutusCore.Rename
import qualified Language.PlutusCore.TypeCheck          as PLC
import qualified Language.PlutusCore.TypeCheck.Internal as PLC
import           Language.PlutusCore.Universe
import           Language.PlutusIR
import           Language.PlutusIR.Error
import           Language.PlutusIR.Transform.Rename     ()
import           Language.PlutusIR.TypeCheck.Internal

import           Control.Monad.Except

{- Note [Goal of PIR typechecker]

The PIR typechecker is an extension  of the PLC typechecker; whereas the PLC typechecker
works on PLC terms, the PIR typechecker works on the PIR terms. A PIR term
can be thought of as a superset of the PLC term language: it adds the `LetRec` and `LetNonRec` syntactic
constructs. Because of ths, the PIR typechecker simply extends the PLC typechecker by adding checks
for these two let constructs of PIR.

Since we already have a PIR->PLC compiler, some would say that it would suffice to first compile the PIR to PLC
and then only run the PLC typechecker. While this is mostly true, there are some reasons for having also
the PIR typechecker as an extra step on the compiler pipeline:

- The error-messages can refer to features of PIR syntax which don't exist in PLC, such as let-terms

- Although PIR is an IR and as such is not supposed to be written by humans, we do have some hand-written PIR code
in our examples/samples/testcases that we would like to make sure they typecheck.

- Our deadcode eliminator which works on PIR (in `Language.PlutusIR.Optimizer.Deadcode`) may eliminate ill-typed code, which
would turn, much to a surprise, an ill-typed program to a well-typed one.

- Some lets of the PIR user may be declared as recursive although they do not *have to* be, e.g. `let (rec) x = 3 in`
would be better written as `let (nonrec) x = 3 in`. In such cases we could signal a warning/error (NB: not implemented atm, and probably not the job of the typechecker pass).

- In general, as an extra source of (type) safety.
-}


-- | Infer the type of a term.
inferType
    :: ( AsTypeError e (Term TyName Name uni ()) uni ann, AsTypeErrorExt e uni ann, MonadError e m, MonadQuote m
       , GShow uni, GEq uni, DefaultUni <: uni
       )
    => TypeCheckConfig uni -> Term TyName Name uni ann -> m (Normalized (Type TyName uni ()))
inferType config = rename >=> PLC.runTypeCheckM config . inferTypeM

-- | Check a term against a type.
-- Infers the type of the term and checks that it's equal to the given type
-- throwing a 'TypeError' (annotated with the value of the @ann@ argument) otherwise.
checkType
    :: ( AsTypeError e (Term TyName Name uni ()) uni ann, AsTypeErrorExt e uni ann, MonadError e m, MonadQuote m
       , GShow uni, GEq uni, DefaultUni <: uni
       )
    => TypeCheckConfig uni
    -> ann
    -> Term TyName Name uni ann
    -> Normalized (Type TyName uni ())
    -> m ()
checkType config ann term ty = do
    termRen <- rename term
    PLC.runTypeCheckM config $ checkTypeM ann termRen ty

-- | Infer the type of a program.
inferTypeOfProgram
    :: ( AsTypeError e (Term TyName Name uni ()) uni ann, AsTypeErrorExt e uni ann, MonadError e m, MonadQuote m
       , GShow uni, GEq uni, DefaultUni <: uni
       )
    => TypeCheckConfig uni -> Program TyName Name uni ann -> m (Normalized (Type TyName uni ()))
inferTypeOfProgram config (Program _ term) = inferType config term

-- | Check a program against a type.
-- Infers the type of the program and checks that it's equal to the given type
-- throwing a 'TypeError' (annotated with the value of the @ann@ argument) otherwise.
checkTypeOfProgram
    :: (AsTypeError e (Term TyName Name uni ()) uni ann, AsTypeErrorExt e uni ann, MonadError e m, MonadQuote m
       , GShow uni, GEq uni, DefaultUni <: uni
       )
    => TypeCheckConfig uni
    -> ann
    -> Program TyName Name uni ann
    -> Normalized (Type TyName uni ())
    -> m ()
checkTypeOfProgram config ann (Program _ term) = checkType config ann term
