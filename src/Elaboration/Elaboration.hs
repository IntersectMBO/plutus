{-# OPTIONS -Wall #-}







-- | This module defines how elaboration of programs is performed, as well as
-- how typechecking of programs is performed. Because Plutus has an
-- interleaved elaboration process, where term declaration and typechecking
-- refer to one another, we can't separate the type checking component out
-- into a separate module.

module Elaboration.Elaboration where

import Utils.ABT
import Utils.Elaborator
import Utils.Names
import Utils.Pretty
import Utils.Unifier
import Utils.Vars
import Plutus.Term
import PlutusTypes.ConSig
import PlutusTypes.Type
import Plutus.Program
import qualified PlutusCore.Term as Core
import qualified PlutusCore.Program as Core
import Elaboration.Elaborator
import Elaboration.Unification ()

import Control.Monad.Except
import Control.Monad.State
import Data.Functor.Identity









-------------------------------------------------
-------------------------------------------------
----------------                 ----------------
----------------   ELABORATION   ----------------
----------------                 ----------------
-------------------------------------------------
-------------------------------------------------





-- | We can add a new defined value declaration given a name, core term,
-- and type.

addDeclaration :: Sourced String -> Core.Term -> Type -> Elaborator ()
addDeclaration n def ty = addElab definitions [(n,(def,ty))]


-- | We can add a new type constructor by giving a name and a type constructor
-- signature.

addTypeConstructor :: String -> TyConSig -> Elaborator ()
addTypeConstructor n sig = addElab (signature.typeConstructors) [(n,sig)]


-- | We can add a new data constructor by given a type constructor name, a
-- name for the data constructor, and a list of arg types from which to build
-- a constructor signature.

addConstructor :: String -> ConSig -> Elaborator ()
addConstructor n consig = addElab (signature.dataConstructors) [(n,consig)]





-- | Elaborating a term declaration takes one of two forms, depending on what
-- kind of declaration is being elaborated. A definition of the form
-- @f : A { M }@ is elaborated directly, while a definition of the form
-- @f : A { f x y z = M }@ is first transformed into the former
-- type of declaration, and then elaborated.
--
-- This corresponds to the elaboration judgment
-- @Σ;Δ ⊢ term n type A def M ⊣ Δ'@ which is defined as
--
-- @
--      Σ ⊢ A type   Σ ; Δ ; n : A ⊢ A ∋ M ▹ M'
--    -------------------------------------------
--    Σ ; Δ ⊢ term n type A def M ⊣ Δ, n : A ↦ M'
-- @

elabTermDecl :: TermDeclaration -> Elaborator ()
elabTermDecl (TermDeclaration n ty m) =
  do putElab currentNameBeingDeclared (unsourced n)
     when' (typeInDefinitions n)
         $ throwError ("Term already defined: " ++ showSourced n)
     isType ty
     let def = freeToDefined (In . Decname . User) m
     def' <- extendElab' definitions
               [(n,(error "This should never be used in elaboration.",ty))]
               (\(n',_) -> n' == n)
             $ check def ty
     addDeclaration n def' ty
elabTermDecl (WhereDeclaration n ty preclauses) =
  case preclauses of
    [] -> throwError "Cannot create an empty let-where definition."
    [(ps,xs,b)] | all isVarPat ps
      -> elabTermDecl
           (TermDeclaration
              n
              ty
              (helperFold lamH xs b))
    (ps0,_,_):_
      -> let clauses = [ clauseH xs ps b
                       | (ps,xs,b) <- preclauses
                       ]
             xs0 = [ "x" ++ show i | i <- [0..length ps0-1] ]
         in elabTermDecl
              (TermDeclaration
                 n
                 ty
                 (helperFold
                    lamH
                    xs0
                    (caseH (map (Var . Free . FreeVar) xs0) clauses)))
  where
    isVarPat :: Pattern -> Bool
    isVarPat (Var _) = True
    isVarPat _ = False





-- | Elaboration of a constructor in this variant is a relatively simple
-- process. This corresponds to the elaboration judgment
-- @Σ ⊢ c A* alt n α* ⊣ Σ'@ which is defined as
--
-- @
--                    Σ ; α* type ⊢ Ai type
--    -------------------------------------------------------
--    Σ ⊢ c A0 ... Ak alt n α* ⊣ Σ, c : [α*](A0,...,Ak)(n α*)
-- @
--
-- Because constructor signatures are a bundle in this implementation, we
-- define this in terms of the judgment @Γ ⊢ [α*](A0,...,An)B consig@ which
-- is implemented in the @checkifyConsig@ function.

elabAlt :: String -> ConSig -> Elaborator ()
elabAlt n consig =
  do when' (typeInSignature n)
         $ throwError ("Constructor already declared: " ++ n)
     checkifyConSig consig
     addConstructor n consig





-- | Elaboration of a type constructor is similar to elaborating a data
-- constructor, except it includes elaborations for the constructors as well.
--
-- @
--    Σ, n : *^k ⊢ C0 alt n α* ⊣ Σ'0
--    Σ'0 ⊢ C1 alt n α* ⊣ Σ'1
--    ...
--    Σ'j-1 ⊢ Cj alt n α* ⊣ Σ'j
--    --------------------------------------
--    Σ ⊢ type n α* alts C0 | ... | Cj ⊣ Σ'j
-- @
--
-- where here @Σ # c@ means that @c@ is not a type constructor in @Σ@.

elabTypeDecl :: TypeDeclaration -> Elaborator ()
elabTypeDecl (TypeDeclaration tycon params alts) =
  do when' (tyconExists tycon)
         $ throwError ("Type constructor already declared: " ++ tycon)
     addTypeConstructor tycon (TyConSig (length params))
     mapM_ (uncurry elabAlt) alts





-- Elaborating a whole program involves chaining together the elaborations of
-- each kind of declaration. We can define it inductively as follows:
--
-- @
--    -----------------
--    Σ ; Δ ⊢ ε ⊣ Σ ; Δ
--
--    Σ ⊢ type n α* alts C0 | ... Ck ⊣ Σ'   Σ' ; Δ ⊢ P ⊣ Σ'' ; Δ''
--    ------------------------------------------------------------
--        Σ ; Δ ⊢ data n α* = { C0 | ... | Ck} ; P ⊣ Σ'' ; Δ''
--
--    Σ ; Δ ⊢ term n type A def M ⊣ Δ'   Σ ; Δ' ⊢ P ⊣ Σ'' ; Δ''
--    ---------------------------------------------------------
--               Σ ; Δ ⊢ x : A { M } ; P ⊣ Σ'' ; Δ''
-- @

elabProgram :: Program -> Elaborator Core.Program
elabProgram (Program stmts0) =
  do go stmts0
     Signature tyConSigs conSigs <- getElab signature
     defs <- getElab definitions
     return $ Core.Program
              { Core.typeConstructors = tyConSigs
              , Core.constructors = conSigs
              , Core.termDeclarations =
                  [ Core.TermDeclaration n def ty
                  | (n,(def,ty)) <- defs
                  ]
              }
  where
    go :: [Statement] -> Elaborator ()
    go [] = return ()
    go (TyDecl td:stmts) = do elabTypeDecl td
                              go stmts
    go (TmDecl td:stmts) = do elabTermDecl td
                              go stmts









---------------------------------------------------
---------------------------------------------------
----------------                   ----------------
----------------   TYPE CHECKING   ----------------
----------------                   ----------------
---------------------------------------------------
---------------------------------------------------





-- | We can check that a type constructor exists by looking in the signature.
-- This corresponds to the judgment @Σ ∋ n : *^k@

tyconExists :: String -> TypeChecker TyConSig
tyconExists n =
  do tycons <- getElab (signature.typeConstructors)
     case lookup n tycons of
       Nothing -> throwError $ "Unknown type constructor: " ++ n
       Just sig -> return sig


-- | We can get the consig of a constructor by looking in the signature.
-- This corresponds to the judgment @Σ ∋ n : S@

typeInSignature :: String -> TypeChecker ConSig
typeInSignature n =
  do consigs <- getElab (signature.dataConstructors)
     case lookup n consigs of
       Nothing -> throwError $ "Unknown constructor: " ++ n
       Just t  -> return t


-- | We can get the signature of a built-in by looking in the signature.
-- This corresponds to the judgment @Σ ∋ !n : S@

builtinInSignature :: String -> TypeChecker ConSig
builtinInSignature n =
  do case lookup n builtinSigs of
       Nothing -> throwError $ "Unknown builtin: " ++ n
       Just t  -> return t
  where
    builtinSigs :: [(String,ConSig)]
    builtinSigs =
      [ ("addInt", conSigH [] [intH,intH] intH)
      , ("subtractInt", conSigH [] [intH,intH] intH)
      , ("multiplyInt", conSigH [] [intH,intH] intH)
      , ("divideInt", conSigH [] [intH,intH] intH)
      , ("remainderInt", conSigH [] [intH,intH] intH)
      , ("lessThanInt", conSigH [] [intH,intH] (tyConH "Bool" []))
      , ("equalsInt", conSigH [] [intH,intH] (tyConH "Bool" []))
      , ("intToFloat", conSigH [] [intH] floatH)
      , ("intToByteString", conSigH [] [intH] byteStringH)
      , ("addFloat", conSigH [] [floatH,floatH] floatH)
      , ("subtractFloat", conSigH [] [floatH,floatH] floatH)
      , ("multiplyFloat", conSigH [] [floatH,floatH] floatH)
      , ("divideFloat", conSigH [] [floatH,floatH] floatH)
      , ("lessThanFloat", conSigH [] [floatH,floatH] (tyConH "Bool" []))
      , ("equalsFloat", conSigH [] [floatH,floatH] (tyConH "Bool" []))
      , ("ceiling", conSigH [] [floatH] intH)
      , ("floor", conSigH [] [floatH] intH)
      , ("round", conSigH [] [floatH] intH)
      , ("concatenate", conSigH [] [byteStringH,byteStringH] byteStringH)
      , ("drop", conSigH [] [intH,byteStringH] byteStringH)
      , ("take", conSigH [] [intH,byteStringH] byteStringH)
      , ("sha2_256", conSigH [] [byteStringH] byteStringH)
      , ("sha3_256", conSigH [] [byteStringH] byteStringH)
      , ("equalsByteString",
          conSigH [] [byteStringH,byteStringH] (tyConH "Bool" []))
      , ("verifySignature",
          conSigH [] [byteStringH,byteStringH,byteStringH] (tyConH "Bool" []))
      , ("transactionInfo", conSigH [] [] (tyConH "Comp" [byteStringH]))
      ]


-- | We can get the type of a declared name by looking in the definitions.
-- This corresponds to the judgment @Δ ∋ n : A@

typeInDefinitions :: Sourced String -> TypeChecker Type
typeInDefinitions n =
  do defs <- getElab definitions
     case lookup n defs of
       Nothing -> throwError $ "Unknown constant/defined term: "
                            ++ showSourced n
       Just (_,t) -> return t


-- | We can get the type of a generated variable by looking in the context.
-- This corresponds to the judgment @Γ ∋ x : A@

typeInContext :: FreeVar -> TypeChecker Type
typeInContext x@(FreeVar n) =
  do ctx <- getElab context
     case lookup x ctx of
       Nothing -> throwError $ "Unbound variable: " ++ n
       Just t -> return t


-- | We can check if a type variable is in scope. This corresponds to the
-- judgment @Γ ∋ α type@

tyVarExists :: FreeVar -> TypeChecker ()
tyVarExists x@(FreeVar n) =
  do tyVarCtx <- getElab tyVarContext
     case lookup x tyVarCtx of
       Nothing -> throwError $ "Unbound type variable: " ++ n
       Just _ -> return ()





-- | Type well-formedness corresponds to the judgment @A type@. This throws a
-- Haskell error if it encounters a variable because there should be no
-- vars in this type checker. That would only be possible for types coming
-- from outside the parser. Same for metavariables.
--
-- The judgment @Σ;Γ ⊢ A type@ is defined inductively as follows:
--
-- @
--   Γ ∋ α type
--   ----------
--   Γ ⊢ α type
--  
--   A type   B type
--   ---------------
--     A → B type
--
--   Σ ∋ n : *^k   Σ ⊢ Ai type
--   -------------------------
--     Σ ⊢ n A0 ... Ak type
--
--   Γ, α type ⊢ A type
--   ------------------
--     Γ ⊢ ∀α. A type
-- @

isType :: Type -> TypeChecker ()
isType (Var (Free x)) =
  tyVarExists x
isType (Var (Bound _ _)) =
  error "Bound type variables should not be the subject of type checking."
isType (Var (Meta _)) =
  error "Metavariables should not be the subject of type checking."
isType (In (TyCon c as)) =
  do TyConSig ar <- tyconExists c
     let las = length as
     unless (ar == las)
       $ throwError $ c ++ " expects " ++ show ar ++ " "
                   ++ (if ar == 1 then "arg" else "args")
                   ++ " but was given " ++ show las
     mapM_ (isType.instantiate0) as
isType (In (Fun a b)) =
  do isType (instantiate0 a)
     isType (instantiate0 b)
-- isType (In (Forall sc)) =
--   do ([x],_,a) <- open tyVarContext sc
--      extendElab tyVarContext [(x,())]
--        $ isType a
isType (In (Comp a)) =
  isType (instantiate0 a)
isType (In PlutusInt) =
  return ()
isType (In PlutusFloat) =
  return ()
isType (In PlutusByteString) =
  return ()





-- | We can instantiate the argument and return types for a constructor
-- signature with variables.

instantiateParams :: [Scope TypeF] -> Scope TypeF -> TypeChecker ([Type],Type)
instantiateParams argscs retsc =
  do metas <- replicateM
               (length (names retsc))
               (nextElab nextMeta)
     let ms = map (Var . Meta) metas
     return ( map (\sc -> instantiate sc ms) argscs
            , instantiate retsc ms
            )





-- | We can instantiate a universally quantified type with metavariables
-- eliminating all the initial quantifiers. For example, the type
-- @∀α,β. (α → β) → α@ would become @(?0 → ?1) → ?0@, while the type
-- @∀α. (∀β. α → β) → α@ would become @(∀β. ?0 → β) → ?0@ and the type
-- @A → ∀β. A → β@ would be unchanged.

instantiateQuantifiers :: Type -> TypeChecker Type
-- instantiateQuantifiers (In (Forall sc)) =
--   do meta <- nextElab nextMeta
--      let m = Var (Meta meta)
--      instantiateQuantifiers (instantiate sc [m])
instantiateQuantifiers t = return t





-- | Let lifting is performed by abstracting over the free variables of a
-- @let@'s value, lifting the now closed term to a top level declaration, and
-- replacing the whole value with an application applied to the free
-- variables. For example, instead of having
--
-- @
--    let f : A -> B { \x -> y } in M
-- @
--
-- where @y@ is free in the definition of @f@, we instead would get something
-- like this:
--
-- @
--    let f : A -> B { f_helper y } in M
-- @
--
-- together with a top-level declaration
--
-- @
--    f_helper : B -> A -> B { \y x -> y }
-- @
--
-- The result of let lifting is that all local @let@s in Core are simple
-- non-recursive codes for substitutions, and all recursive definitions are
-- top-level declarations of functions.
--
-- Let lifting implements the judgment @Δ ⊢ n : A { M } lifts M' ⊣ Δ'@
-- which is defined as
--
-- @
--    Δ ⊢ helper : Γ* → A { λΓ*.M } ⊣ Δ'    Δ' ; Γ* ⊢ A ∋ helper Γ* ▹ M'
--    ------------------------------------------------------------------
--                     Δ ⊢ n : A { M } lifts M' ⊣ Δ''
-- @
--
-- where @helper@ is some globally unique name generated for the lifting
-- process, @Γ* → A@ is the iterated function type which has the @Γ*@s as the
-- arguments before @A@, @λΓ*.M@ is the function with iterated abstractions
-- over the variables of @Γ*@, and @helper Γ*@ is iterated application. For
-- the above example, @Γ* = y : B@.

letLift :: String -> Term -> Type -> TypeChecker Core.Term
letLift liftName m a =
  do let fvs = freeVars m
     i <- nextElab nextGeneratedNameIndex
     currentName <- getElab currentNameBeingDeclared
     ctx <- getElab context
     let helperName :: Sourced String
         helperName =
             Generated (currentName ++ "_" ++ liftName ++ "_" ++ show i)
         fvsWithTypes :: [(FreeVar,Type)]
         fvsWithTypes = [ (fv,t)
                        | fv <- fvs
                        , fv /= FreeVar liftName
                        , let Just t = lookup fv ctx
                        ]
         helperType :: Type
         helperType = helperFold
                        (\(_,b) c -> funH b c)
                        fvsWithTypes
                        a
         newM :: Term
         newM = helperFold
                  (\(x,_) f -> appH f (Var (Free x)))
                  fvsWithTypes
                  (decnameH helperName)
         helperDef :: Term
         helperDef = helperFold
                       (\(FreeVar x,_) b -> lamH x b)
                       fvsWithTypes
                       (runIdentity (swapName m))
         swapName :: Term -> Identity Term
         swapName (Var v) = Identity (Var v)
         swapName (In (Decname x))
           | x == User liftName =
               Identity newM
           | otherwise =
               Identity (In (Decname x))
         swapName (In x) = In <$> traverse (underF swapName) x
     elabTermDecl
       (TermDeclaration helperName helperType helperDef)
     checkify newM a





-- | Type synthesis corresponds to the judgment @Γ ⊢ M ▹ M' ∈ A@. This throws
-- a Haskell error when trying to synthesize the type of a bound variable,
-- because all bound variables should be replaced by free variables during
-- this part of type checking.
--
-- The judgment @Γ ⊢ M ▹ M' ∈ A@ is defined inductively as follows:
--
-- @
--      Γ ∋ x : A
--    ------------- variable
--    Γ ⊢ x ▹ x ∈ A
--
--          Δ ∋ n : A
--    ---------------------- definition
--    Δ ⊢ n ▹ decname[n] ∈ A
--
--    A type   A ∋ M ▹ M'
--    ------------------- annotation
--      M : A ▹ M' ∈ A
--
--    M ▹ M' ∈ A → B   A ∋ N ▹ N'
--    --------------------------- application
--        M N ▹ app(M';N') ∈ B
--
--    Mi ▹ M'i ∈ Ai   Pj → Nj ▹ N'j from A0,...,Am to B
--    -------------------------------------------------- case
--    case M0 | ... | Mm of { P0 → N0; ...; Pn → Nn }
--    ▹ case(M'0,...,M'm; cl(P0,N'0),...,cl(Pn;N'n)) ∈ B
--
--    Σ ∋ n : [α*](A0,...,Ak)B
--    [σ]B = B'
--    Σ ⊢ [σ]Ai ∋ Mi ▹ M'
--    ---------------------------------------------- builtin
--    Σ ⊢ !n M0 ... Mk ▹ builtin[n](M'0,...,M'k) ∈ B
-- @
--
-- Not everything is officially synthesizable but is supported here to be as
-- user friendly as possible. Successful synthesis relies on the unification
-- mechanism to fully instantiate types. The pseudo-rules that ares used are
--
-- @
--    Δ ⊢ x : A { M } lifts M' ⊣ Δ'    Δ' ; Γ, x : A ⊢ N ▹ N' ∈ B ⊣ Δ''
--    ----------------------------------------------------------------- let
--          Δ ; Γ ⊢ let x : A { M } in N ▹ let(M';x.N') ∈ B ⊣ Δ''
--
--       Γ, x : A ⊢ M ▹ M' ∈ B
--    ---------------------------- function
--    Γ ⊢ λx → M ▹ λ(x.M') ∈ A → B
--
--    Σ ∋ n : [α*](A0,...,An)B
--    [σ]B = B'
--    Σ ⊢ [σ]Ai ∋ Mi ▹ M'i
--    ------------------------------------------ constructed data
--    Σ ⊢ B' ∋ n M0 ... Mn ▹ con[n](M'0,...,M'n)
--
--              Γ ⊢ M ▹ M' ∈ A
--    ------------------------------------ success
--    Γ ⊢ success M ▹ success(M') ∈ Comp A
--
--    ------------------------------ failure
--    Γ ⊢ failure ▹ failure ∈ Comp A
--
--    Γ ⊢ M ▹ M' ∈ Comp A   Γ, x : A ⊢ N ▹ N' ∈ Comp B
--    ------------------------------------------------ bind
--     Γ ⊢ do { x <- M ; N } ▹ bind(M';x.N') ∈ Comp B
-- @

synthify :: Term -> TypeChecker (Core.Term, Type)
synthify (Var (Bound _ _)) =
  error "A bound variable should never be the subject of type synthesis."
synthify (Var (Free n)) =
  do t <- typeInContext n
     return (Var (Free n), t)
synthify (Var (Meta _)) =
  error "Metavariables should not be the subject of type synthesis."
synthify (In (Decname x)) =
  do t <- typeInDefinitions x
     return (Core.decnameH x, t)
synthify (In (Ann m t)) =
  do isType t
     m' <- checkify (instantiate0 m) t
     subs <- getElab substitution
     return (Core.substTypeMetas subs m', substMetas subs t)
synthify (In (Let a m sc)) =
  do m' <- letLift (head (names sc)) (instantiate0 m) a
     ([x],[v],n) <- open context sc
     (n',b) <- extendElab context [(x,a)]
                 $ synthify n
     return (Core.letH m' v n', b)
synthify (In (Lam sc)) =
  do meta <- nextElab nextMeta
     let arg = Var (Meta meta)
     ([x],[n],m) <- open context sc
     (m',ret) <- extendElab context [(x,arg)]
                   $ synthify m
     subs <- getElab substitution
     return ( Core.substTypeMetas subs (Core.lamH arg n m')
            , substMetas subs (funH arg ret)
            )
synthify (In (App f a)) =
  do (f', t) <- synthify (instantiate0 f)
     t' <- instantiateQuantifiers t
     case t' of
       In (Fun arg ret) -> do
         a' <- checkify (instantiate0 a) (instantiate0 arg)
         subs <- getElab substitution
         return ( Core.substTypeMetas subs (Core.appH f' a')
                , substMetas subs (instantiate0 ret)
                )
       _ -> throwError $ "Expected a function type when checking"
                      ++ " the expression: " ++ pretty (instantiate0 f)
                      ++ "\nbut instead found: " ++ pretty t'
synthify (In (Con c as)) =
  do ConSig argscs retsc <- typeInSignature c
     (args',ret') <- instantiateParams argscs retsc
     let las = length as
         largs' = length args'
     unless (las == largs')
       $ throwError $ c ++ " expects " ++ show largs' ++ " "
                 ++ (if largs' == 1 then "arg" else "args")
                 ++ " but was given " ++ show las
     as' <- checkifyMulti (map instantiate0 as) args'
     subs <- getElab substitution
     return ( Core.substTypeMetas subs (Core.conH c as')
            , substMetas subs ret'
            )
synthify (In (Case ms cs)) =
  do (ms', as) <- unzip <$> mapM (synthify.instantiate0) ms
     (cs', b) <- synthifyClauses as cs
     return (Core.caseH ms' cs', b)
synthify (In (Success m)) =
  do (m',a) <- synthify (instantiate0 m)
     return (Core.successH m', compH a)
synthify (In Failure) =
  do meta <- nextElab nextMeta
     return ( Core.failureH (Var (Meta meta))
            , compH (Var (Meta meta))
            )
synthify (In (Bind m sc)) =
  do (m',ca) <- synthify (instantiate0 m)
     case ca of
       In (Comp a) -> do
         do ([x],[v],n) <- open context sc
            (n',cb) <- extendElab context [(x,instantiate0 a)]
                         $ synthify n
            case cb of
              In (Comp b) ->
                return (Core.bindH m' v n', In (Comp b))
              _ ->
                throwError $ "Expected a computation type but found "
                      ++ pretty cb ++ "\nWhen checking term " ++ pretty n
       _ -> throwError $ "Expected a computation type but found " ++ pretty ca
                      ++ "\nWhen checking term " ++ pretty (instantiate0 m)
synthify (In (PrimData (PrimInt x))) =
  return (Core.primIntH x, intH)
synthify (In (PrimData (PrimFloat x))) =
  return (Core.primFloatH x, floatH)
synthify (In (PrimData (PrimByteString x))) =
  return (Core.primByteStringH x, byteStringH)
synthify (In (Builtin n as)) =
  do ConSig argscs retsc <- builtinInSignature n
     (args',ret') <- instantiateParams argscs retsc
     let las = length as
         largs' = length args'
     unless (las == largs')
       $ throwError $ n ++ " expects " ++ show largs' ++ " "
                 ++ (if largs' == 1 then "arg" else "args")
                 ++ " but was given " ++ show las
     as' <- checkifyMulti (map instantiate0 as) args'
     subs <- getElab substitution
     return ( Core.substTypeMetas subs (Core.builtinH n as')
            , substMetas subs ret'
            )





-- | Type synthesis for clauses corresponds to the judgment
-- @Σ;Δ;Γ ⊢ P* → M ▹ M' from A* to B@.
--
-- The judgment @Σ;Δ;Γ ⊢ P* → M ▹ P'* → M' from A* to B@ is defined as follows:
--
-- @
--    Σ ⊢ Ai pattern Pi ▹ P'i ⊣ Γ'i
--    Σ ; Δ ; Γ, Γ'0, ..., Γ'k ⊢ B ∋ M ▹ M'
--    ------------------------------------------ clause
--    Σ ; Δ ; Γ ⊢ P0 | ... | Pk → M ▹
--      P'0 | ... | P'k → M' from A0,...,Ak to B
-- @

synthifyClause :: [Type] -> Clause -> TypeChecker (Core.Clause, Type)
synthifyClause patTys (Clause pscs sc) =
  do let lps = length pscs
     unless (length patTys == lps)
       $ throwError $ "Mismatching number of patterns. Expected "
                   ++ show (length patTys)
                   ++ " but found " ++ show lps
     metas <- replicateM (length (names sc))
                         (nextElab nextMeta)
     let args = [ Var (Meta meta) | meta <- metas ]
     pscs' <- forM (zip pscs patTys) $ \(psc,patTy) -> do
                subs <- getElab substitution
                (xs,ns,p) <- open context psc
                p' <- extendElab
                        context
                        (zip xs (map (substMetas subs) args))
                        (checkifyPattern p (substMetas subs patTy))
                return $ scope ns p'
     subs <- getElab substitution
     (xs,ns,m) <- open context sc
     (m',ret) <- extendElab context (zip xs (map (substMetas subs) args))
                   $ synthify m
     subs' <- getElab substitution
     return ( Core.substTypeMetasClause subs' (Core.Clause pscs' (scope ns m'))
            , substMetas subs' ret
            )





-- | The monadic generalization of 'synthClause', ensuring that there's at
-- least one clause to check, and that all clauses have the same result type.

synthifyClauses :: [Type] -> [Clause] -> TypeChecker ([Core.Clause], Type)
synthifyClauses patTys cs =
  do (cs',ts) <- unzip <$> mapM (synthifyClause patTys) cs
     case ts of
       [] -> throwError "Empty clauses."
       t:ts' -> do
         catchError (mapM_ (unify substitution context t) ts') $ \e ->
           throwError $ "Clauses do not all return the same type:\n"
                     ++ unlines (map pretty ts) ++ "\n"
                     ++ "Unification failed with error: " ++ e
         subs <- getElab substitution
         return ( map (Core.substTypeMetasClause subs) cs'
                , substMetas subs t
                )





-- | Type checking corresponds to the judgment @Γ ⊢ A ∋ M ▹ M'@.
--
-- The judgment @Γ ⊢ A ∋ M ▹ M'@ is defined inductively as follows:
--
-- @
--    Δ ⊢ x : A { M } lifts M' ⊣ Δ'    Δ' ; Γ, x : A ⊢ B ∋ N ▹ N' ⊣ Δ''
--    ----------------------------------------------------------------- let
--          Δ ; Γ ⊢ B ∋ let x : A { M } in N ▹ let(M';x.N') ⊣ Δ''
--
--       Γ, x : A ⊢ B ∋ M ▹ M'
--    --------------------------- lambda
--    Γ ⊢ A → B ∋ λx → M ▹ λ(x.M')
--
--    Σ ∋ n : [α*](A0,...,Ak)B
--    [σ]B = B'
--    Σ ⊢ [σ]Ai ∋ Mi ▹ M'i
--    ------------------------------------------ constructed data
--    Σ ⊢ B' ∋ n M0 ... Mn ▹ con[n](M'0,...,M'k)
--
--               A ∋ M ▹ M'
--    -------------------------------- success
--    Comp A ∋ success M ▹ success(M')
--
--    -------------------------- failure
--    Comp A ∋ failure ▹ failure
--
--    Γ ⊢ M ▹ M' ∈ Comp A   Γ, x : A ⊢ Comp B ∋ N ▹ N'
--    ------------------------------------------------ bind
--     Γ ⊢ Comp B ∋ do { x  ← M ; N } ▹ bind(M';x.N')
--
--    Γ, α type ⊢ A ∋ M ▹ M'
--    ---------------------- forall
--      Γ ⊢ ∀α.A ∋ M ▹ M'
--
--    M ▹ M' ∈ A   A ⊑ B
--    ------------------ direction change
--        B ∋ M ▹ M'
-- @

checkify :: Term -> Type -> TypeChecker Core.Term
-- checkify m (In (Forall sc)) =
--   do ([a],_,b) <- open tyVarContext sc
--      extendElab tyVarContext [(a,())]
--        $ checkify m b
checkify (In (Let a m sc)) b =
  do m' <- letLift (head (names sc)) (instantiate0 m) a
     ([x],[v],n) <- open context sc
     n' <- extendElab context [(x,a)]
             $ checkify n b
     return $ Core.letH m' v n'
checkify (In (Lam sc)) (In (Fun arg ret)) =
  do ([x],[v],m) <- open context sc
     m' <- extendElab context [(x,instantiate0 arg)]
             $ checkify m (instantiate0 ret)
     subs <- getElab substitution
     return $ Core.substTypeMetas subs (Core.lamH (instantiate0 arg) v m')
checkify (In (Lam sc)) t =
  throwError $ "Cannot check term: " ++ pretty (In (Lam sc)) ++ "\n"
            ++ "Against non-function type: " ++ pretty t
checkify (In (Con c as)) b =
  do ConSig argscs retsc <- typeInSignature c
     (args',ret') <- instantiateParams argscs retsc
     let las = length as
         largs' = length args'
     unless (las == largs')
       $ throwError $ c ++ " expects " ++ show largs' ++ " "
                 ++ (if largs' == 1 then "arg" else "args")
                 ++ " but was given " ++ show las
     unify substitution context b ret'
     subs <- getElab substitution
     as' <- checkifyMulti (map instantiate0 as)
                          (map (substMetas subs) args')
     return $ Core.conH c as'
checkify (In (Success m)) (In (Comp a)) =
  do m' <- checkify (instantiate0 m) (instantiate0 a)
     return $ Core.successH m'
checkify (In (Success m)) a =
  throwError $ "Cannot check term: " ++ pretty (In (Success m)) ++ "\n"
            ++ "Against non-computation type: " ++ pretty a
checkify (In Failure) (In (Comp a)) =
  return $ Core.failureH (In (Comp a))
checkify (In Failure) a =
  throwError $ "Cannot check term: " ++ pretty (In Failure) ++ "\n"
            ++ "Against non-computation type: " ++ pretty a
checkify (In (Bind m sc)) (In (Comp b)) =
  do (m',ca) <- synthify (instantiate0 m)
     case ca of
       In (Comp a) -> do
         do ([x],[v],n) <- open context sc
            n' <- extendElab context [(x,instantiate0 a)]
                    $ checkify n (In (Comp b))
            return $ Core.bindH m' v n'
       _ -> throwError $ "Expected a computation type but found " ++ pretty ca
                      ++ "\nWhen checking term " ++ pretty (instantiate0 m)
checkify (In (Bind m sc)) b =
  throwError $ "Cannot check term: " ++ pretty (In (Bind m sc)) ++ "\n"
            ++ "Against non-computation type: " ++ pretty b
checkify (In (PrimData (PrimInt x))) (In PlutusInt) =
  return $ Core.primIntH x
checkify m@(In (PrimData (PrimInt _))) a =
  throwError $ "Cannot check int: " ++ pretty m ++ "\n"
            ++ "Against non-integer type: " ++ pretty a
checkify (In (PrimData (PrimFloat x))) (In PlutusFloat) =
  return $ Core.primFloatH x
checkify m@(In (PrimData (PrimFloat _))) a =
  throwError $ "Cannot check float: " ++ pretty m ++ "\n"
            ++ "Against non-float type: " ++ pretty a
checkify (In (PrimData (PrimByteString x))) (In PlutusByteString) =
  return $ Core.primByteStringH x
checkify m@(In (PrimData (PrimByteString _))) a =
  throwError $ "Cannot check byteString: " ++ pretty m ++ "\n"
            ++ "Against non-byteString type: " ++ pretty a
checkify m t =
  do (m',t') <- synthify m
     subtype t' t
     return m'





-- | Checkifying a sequence of terms involves chaining substitutions
-- appropriately. This doesn't correspond to a particular judgment so much
-- as a by product of the need to explicitly propagate the effects of
-- unification.

checkifyMulti :: [Term] -> [Type] -> TypeChecker [Core.Term]
checkifyMulti [] [] = return []
checkifyMulti (m:ms) (t:ts) =
  do subs <- getElab substitution
     m' <- checkify m (substMetas subs t)
     ms' <- checkifyMulti ms ts
     return $ m':ms'
checkifyMulti _ _ =
  throwError "Mismatched constructor signature lengths."






-- | This function checks if the first type is a subtype of the second. This
-- corresponds to the judgment @S ⊑ T@ which is defined inductively as:
--
-- @
--     A ⊑ B
--    --------
--    A ⊑ ∀α.B
--
--    [T/α]A ⊑ B
--    ----------
--     ∀α.A ⊑ B
--
--    A' ⊑ A   B ⊑ B'
--    ---------------
--    A → B ⊑ A' → B'
--
--    -----
--    A ⊑ A
-- @

subtype :: Type -> Type -> TypeChecker ()
-- subtype a (In (Forall sc')) =
--   do (_,_,b) <- open tyVarContext sc'
--      subtype a b
-- subtype (In (Forall sc)) b =
--   do meta <- nextElab nextMeta
--      subtype (instantiate sc [Var (Meta meta)]) b
-- subtype (In (Fun arg ret)) (In (Fun arg' ret')) =
--   do subtype (instantiate0 arg') (instantiate0 arg)
--      subtype (instantiate0 ret) (instantiate0 ret')
subtype a b =
  unify substitution context a b





-- | Type checking for patterns corresponds to the judgment
-- @Σ ⊢ A pattern P ▹ P' ⊣ Γ'@, where @Γ'@ is an output context.
--
-- The judgment @Σ ⊢ A pattern P ▹ P' ⊣ Γ'@ is defined inductively as follows:
--
-- @
--    ---------------------------
--    Σ ⊢ A pattern x ▹ x ⊣ x : A
--
--    Σ ∋ n : [α*](A0,...,Ak)B
--    [σ]B = B'
--    Σ ⊢ Ai pattern Pi ▹ P'i ⊣ Γ'i
--    -----------------------------------
--    Σ ⊢ B' pattern n P0 ... Pk ▹
--      con[n](P'0,...,P'k) ⊣ Γ'0,...,Γ'k
--
--    primitive V has type A
--    -----------------------
--    Σ ⊢ A pattern V ▹ V ⊣ ε
-- @

checkifyPattern :: Pattern -> Type -> TypeChecker Core.Pattern
checkifyPattern (Var (Bound _ _)) _ =
  error "A bound variable should not be the subject of pattern type checking."
checkifyPattern (Var (Meta _)) _ =
  error "Metavariables should not be the subject of type checking."
checkifyPattern (Var (Free n)) t =
  do t' <- typeInContext n
     unify substitution context t t'
     return $ Var (Free n)
checkifyPattern (In (ConPat c ps)) t =
  do ConSig argscs retsc <- typeInSignature c
     (args',ret') <- instantiateParams argscs retsc
     let lps = length ps
         largs' = length args'
     unless (lps == largs')
       $ throwError $ c ++ " expects " ++ show largs' ++ " "
                 ++ (if largs' == 1 then "arg" else "args")
                 ++ " but was given " ++ show lps
     unify substitution context t ret'
     subs <- getElab substitution
     ps' <- zipWithM
              checkifyPattern
              (map instantiate0 ps)
              (map (substMetas subs) args')
     return $ Core.conPatH c ps'
checkifyPattern (In (PrimPat (PrimInt x))) (In PlutusInt) =
  return $ Core.primIntPatH x
checkifyPattern m@(In (PrimPat (PrimInt _))) a =
  throwError $ "Cannot check int pattern: " ++ pretty m ++ "\n"
            ++ "Against non-integer type: " ++ pretty a
checkifyPattern (In (PrimPat (PrimFloat x))) (In PlutusFloat) =
  return $ Core.primFloatPatH x
checkifyPattern m@(In (PrimPat (PrimFloat _))) a =
  throwError $ "Cannot check float pattern: " ++ pretty m ++ "\n"
            ++ "Against non-float type: " ++ pretty a
checkifyPattern (In (PrimPat (PrimByteString x))) (In PlutusByteString) =
  return $ Core.primByteStringPatH x
checkifyPattern m@(In (PrimPat (PrimByteString _))) a =
  throwError $ "Cannot check byteString pattern: " ++ pretty m ++ "\n"
            ++ "Against non-byteString type: " ++ pretty a





-- | Type checking of constructor signatures corresponds to the judgment
-- @Γ ⊢ [α*](A0,...,Ak)B consig@ which is defined as
--
-- @
--    Γ, α* type ⊢ Ai type   Γ, α* type ⊢ B type
--    ------------------------------------------
--           Γ ⊢ [α*](A0,...,An)B consig
-- @
--
-- Because of the ABT representation, however, the scope is pushed down inside
-- the 'ConSig' constructor, onto its arguments.
--
-- This synthesis rule is not part of the spec proper, but rather is a
-- convenience method for the elaboration process because constructor
-- signatures are already a bunch of information in the implementation.

checkifyConSig :: ConSig -> TypeChecker ()
checkifyConSig (ConSig argscs retsc) =
  do forM_ argscs $ \argsc -> do
       (xs,_,a) <- open tyVarContext argsc
       extendElab tyVarContext [ (x,()) | x <- xs ]
         $ isType a
     (xs,_,b) <- open tyVarContext retsc
     extendElab tyVarContext [ (x,()) | x <- xs ]
       $ isType b





-- | All metavariables have been solved when the next metavar to produces is
-- the number of substitutions we've found.

metasSolved :: TypeChecker ()
metasSolved = do s <- get
                 unless (_nextMeta s == MetaVar (length (_substitution s)))
                   $ throwError "Not all metavariables have been solved."





-- | Checking is just checkifying with a requirement that all metas have been
-- solved.

check :: Term -> Type -> TypeChecker Core.Term
check m t = do m' <- checkify m t
               metasSolved
               subs <- getElab substitution
               return $ Core.substTypeMetas subs m'





-- | Synthesis is just synthifying with a requirement that all metas have been
-- solved. The returned type is instantiated with the solutions.

synth :: Term -> TypeChecker (Core.Term,Type)
synth m = do (m',t) <- synthify m
             metasSolved
             subs <- getElab substitution
             return ( Core.substTypeMetas subs m'
                    , substMetas subs t
                    )