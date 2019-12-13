-- | A monadic interface for the Z3 API
-- | 
-- | Takes care of reference counting and provides a cleaner API
-- | ```
-- | run :: Effect Boolean
-- | run =
-- |   runZ3 do
-- |     x <- mkIntVar "x"
-- |     y <- mkIntVar "y"
-- |     ast <- not =<< eq x.ast y.ast
-- |     assert ast
-- |     push
-- |     res <- check
-- |     _ <-
-- |       if res then do
-- |         modelX <- withModel \model -> getAstFromModel model x.decl
-- |         modelXString <- astToString modelX
-- |         let
-- |           n = readInt 10 modelXString
-- |         trace n \_ -> pure res
-- |       else
-- |         pure res
-- |     pop
-- |     ast2 <- eq x.ast y.ast
-- |     assert ast2
-- |     check
-- | ```
module Z3.Monad where

import Prelude
import Data.Function.Uncurried (runFn1, runFn2, runFn3, runFn4)
import Data.Newtype (class Newtype)
import Effect (Effect)
import Z3.Internal (Z3Ast, Z3Config, Z3Context, Z3FuncDecl, Z3Instance, Z3Model, Z3Solver)
import Z3.Internal as Z3

newtype Z3 a
  = Z3 (State -> a)

derive instance newtypeZ3 :: Newtype (Z3 a) _

derive newtype instance functorZ3 :: Functor Z3

derive newtype instance applyZ3 :: Apply Z3

derive newtype instance applicativeZ3 :: Applicative Z3

derive newtype instance bindZ3 :: Bind Z3

derive newtype instance monadZ3 :: Monad Z3

type State
  = { cfg :: Z3Config
    , ctx :: Z3Context
    , solver :: Z3Solver
    , z3 :: Z3Instance
    }

runZ3 :: forall a. Z3 a -> Effect a
runZ3 (Z3 f) = do
  z3 <- Z3.createInstance
  let
    cfg = runFn1 Z3.mk_config z3

    ctx = runFn2 Z3.mk_context z3 cfg

    solver = runFn2 Z3.mk_solver z3 ctx

    _ = runFn3 Z3.solver_inc_ref z3 ctx solver

    state = { z3, cfg, ctx, solver }

    res = f state

    _ = runFn3 Z3.solver_dec_ref z3 ctx solver

    _ = runFn2 Z3.del_config z3 cfg

    _ = runFn2 Z3.del_context z3 ctx
  pure res

push :: Z3 Unit
push = Z3 \state -> runFn3 Z3.solver_push state.z3 state.ctx state.solver

pop :: Z3 Unit
pop = Z3 \state -> runFn3 Z3.solver_pop state.z3 state.ctx state.solver

mkIntVar :: String -> Z3 { decl :: Z3FuncDecl, ast :: Z3Ast }
mkIntVar name =
  Z3 \state ->
    let
      sym = runFn3 Z3.mk_string_symbol state.z3 state.ctx name

      sort = runFn2 Z3.mk_int_sort state.z3 state.ctx

      decl = runFn4 Z3.mk_func_decl state.z3 state.ctx sym sort

      ast = runFn3 Z3.mk_app state.z3 state.ctx decl
    in
      { decl, ast }

not :: Z3Ast -> Z3 Z3Ast
not ast = Z3 \state -> runFn3 Z3.mk_not state.z3 state.ctx ast

eq :: Z3Ast -> Z3Ast -> Z3 Z3Ast
eq x y = Z3 \state -> runFn4 Z3.mk_eq state.z3 state.ctx x y

assert :: Z3Ast -> Z3 Unit
assert x = Z3 \state -> runFn4 Z3.solver_assert state.z3 state.ctx state.solver x

check :: Z3 Boolean
check =
  Z3 \state ->
    let
      res = runFn3 Z3.solver_check state.z3 state.ctx state.solver
    in
      if res == 1 then true else false

withModel :: forall a. (Z3Model -> Z3 a) -> Z3 a
withModel f = do
  model <- Z3 \state -> runFn3 Z3.solver_get_model state.z3 state.ctx state.solver
  _ <- Z3 \state -> runFn3 Z3.model_inc_ref state.z3 state.ctx model
  res <- f model
  _ <- Z3 \state -> runFn3 Z3.model_inc_ref state.z3 state.ctx model
  pure res

getAstFromModel :: Z3Model -> Z3FuncDecl -> Z3 Z3Ast
getAstFromModel model decl = Z3 \state -> runFn4 Z3.model_get_const_interp state.z3 state.ctx model decl

astToString :: Z3Ast -> Z3 String
astToString ast = Z3 \state -> runFn3 Z3.ast_to_string state.z3 state.ctx ast
