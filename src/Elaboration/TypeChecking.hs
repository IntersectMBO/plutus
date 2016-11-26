{-# OPTIONS -Wall #-}







-- | A unification-based type checker. It's worth noting that this language is
-- not System F, as it lacks syntax for type abstraction and type application.
-- Instead, it's more like Haskell with @RankNTypes@.

module Elaboration.TypeChecking where

import Utils.ABT
import Utils.Elaborator
import Utils.Pretty
import Utils.Unifier
import Utils.Vars
import Plutus.ConSig
import Plutus.Term
import Plutus.Type
import qualified PlutusCore.Term as Core
import Elaboration.Elaborator
import Elaboration.Unification ()

import Control.Monad.Except
import Control.Monad.State







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
  do consigs <- getElab (signature.builtins)
     case lookup n consigs of
       Nothing -> throwError $ "Unknown builtin: " ++ n
       Just t  -> return t


-- | We can get the type of a declared name by looking in the definitions.
-- This corresponds to the judgment @Δ ∋ n : A@

typeInDefinitions :: String -> TypeChecker Type
typeInDefinitions n =
  do defs <- getElab definitions
     case lookup n defs of
       Nothing -> throwError $ "Unknown constant/defined term: " ++ n
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
isType (In (Forall sc)) =
  do ([x],_,a) <- open tyVarContext sc
     extendElab tyVarContext [(x,())]
       $ isType a
isType (In (Comp a)) =
  isType (instantiate0 a)





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
instantiateQuantifiers (In (Forall sc)) =
  do meta <- nextElab nextMeta
     let m = Var (Meta meta)
     instantiateQuantifiers (instantiate sc [m])
instantiateQuantifiers t = return t





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
--      Γ ⊢ M ▹ M' ∈ A   Γ, x : A ⊢ N ▹ N' ∈ B
--    ------------------------------------------- let
--    Γ ⊢ let x : A { M } in N ▹ let(M';x.N') ∈ B
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
     return (m', substMetas subs t)
synthify (In (Let a m sc)) =
  do m' <- checkify (instantiate0 m) a
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
     return ( Core.lamH n m'
            , substMetas subs (funH arg ret)
            )
synthify (In (App f a)) =
  do (f', t) <- synthify (instantiate0 f)
     t' <- instantiateQuantifiers t
     case t' of
       In (Fun arg ret) -> do
         a' <- checkify (instantiate0 a) (instantiate0 arg)
         subs <- getElab substitution
         return (Core.appH f' a', substMetas subs (instantiate0 ret))
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
     return (Core.conH c as', substMetas subs ret')
synthify (In (Case ms cs)) =
  do (ms', as) <- unzip <$> mapM (synthify.instantiate0) ms
     (cs', b) <- synthifyClauses as cs
     return (Core.caseH ms' cs', b)
synthify (In (Success m)) =
  do (m',a) <- synthify (instantiate0 m)
     return (Core.successH m', compH a)
synthify (In Failure) =
  do meta <- nextElab nextMeta
     return ( Core.failureH
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
     return (Core.builtinH n as', substMetas subs ret')





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
     return ( Core.Clause pscs' (scope ns m')
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
         return ( cs'
                , substMetas subs t
                )





-- | Type checking corresponds to the judgment @Γ ⊢ A ∋ M ▹ M'e@.
--
-- The judgment @Γ ⊢ A ∋ M ▹ M'@ is defined inductively as follows:
--
-- @
--    Γ ⊢ A type
--    Γ ⊢ A ∋ M ▹ M'
--    Γ, x : A ⊢ B ∋ N ▹ N'
--    ------------------------------------------- let
--    Γ ⊢ B ∋ let x : A { M } in N ▹ let(M';x.N')
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
checkify m (In (Forall sc)) =
  do ([a],_,b) <- open tyVarContext sc
     extendElab tyVarContext [(a,())]
       $ checkify m b
checkify (In (Let a m sc)) b =
  do m' <- checkify (instantiate0 m) a
     ([x],[v],n) <- open context sc
     n' <- extendElab context [(x,a)]
             $ checkify n b
     return $ Core.letH m' v n'
checkify (In (Lam sc)) (In (Fun arg ret)) =
  do ([x],[v],m) <- open context sc
     m' <- extendElab context [(x,instantiate0 arg)]
             $ checkify m (instantiate0 ret)
     return $ Core.lamH v m'
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
checkify (In Failure) (In (Comp _)) =
  return Core.failureH
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
                      ++ "When checking term " ++ pretty (instantiate0 m)
checkify (In (Bind m sc)) b =
  throwError $ "Cannot check term: " ++ pretty (In (Bind m sc)) ++ "\n"
            ++ "Against non-computation type: " ++ pretty b
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
subtype a (In (Forall sc')) =
  do (_,_,b) <- open tyVarContext sc'
     subtype a b
subtype (In (Forall sc)) b =
  do meta <- nextElab nextMeta
     subtype (instantiate sc [Var (Meta meta)]) b
subtype (In (Fun arg ret)) (In (Fun arg' ret')) =
  do subtype (instantiate0 arg') (instantiate0 arg)
     subtype (instantiate0 ret) (instantiate0 ret')
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
               return m'





-- | Synthesis is just synthifying with a requirement that all metas have been
-- solved. The returned type is instantiated with the solutions.

synth :: Term -> TypeChecker (Core.Term,Type)
synth m = do (m',t) <- synthify m
             metasSolved
             subs <- getElab substitution
             return (m', substMetas subs t)