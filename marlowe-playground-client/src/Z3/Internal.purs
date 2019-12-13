-- | The raw API - see https://z3prover.github.io/api/html/group__capi.html
module Z3.Internal where

import Prelude
import Data.Function.Uncurried (Fn1, Fn2, Fn3, Fn4)
import Effect (Effect)

foreign import data Z3Instance :: Type

foreign import data Z3Config :: Type

foreign import data Z3Context :: Type

foreign import data Z3Symbol :: Type

foreign import data Z3Ast :: Type

foreign import data Z3Sort :: Type

foreign import data Z3FuncDecl :: Type

foreign import data Z3App :: Type

foreign import data Z3Pattern :: Type

foreign import data Z3Constructor :: Type

foreign import data Z3ConstructorList :: Type

foreign import data Z3Params :: Type

foreign import data Z3ParamDescrs :: Type

foreign import data Z3Model :: Type

foreign import data Z3FuncInterp :: Type

foreign import data Z3FuncEntry :: Type

foreign import data Z3Fixedpoint :: Type

foreign import data Z3Optimize :: Type

foreign import data Z3Ast_vector :: Type

foreign import data Z3Ast_map :: Type

foreign import data Z3Goal :: Type

foreign import data Z3Tactic :: Type

foreign import data Z3Probe :: Type

foreign import data Z3ApplyResult :: Type

foreign import data Z3Solver :: Type

foreign import data Z3Stats :: Type

foreign import createInstance :: Effect Z3Instance

foreign import mk_config :: Fn1 Z3Instance Z3Config

foreign import mk_context :: Fn2 Z3Instance Z3Config Z3Context

foreign import del_config :: Fn2 Z3Instance Z3Config Unit

foreign import del_context :: Fn2 Z3Instance Z3Context Unit

foreign import mk_solver :: Fn2 Z3Instance Z3Context Z3Solver

foreign import mk_string_symbol :: Fn3 Z3Instance Z3Context String Z3Symbol

foreign import mk_const :: Fn4 Z3Instance Z3Context Z3Symbol Z3Sort Z3Ast

foreign import mk_int_sort :: Fn2 Z3Instance Z3Context Z3Sort

foreign import mk_string_sort :: Fn2 Z3Instance Z3Context Z3Sort

foreign import mk_bool_sort :: Fn2 Z3Instance Z3Context Z3Sort

foreign import mk_int :: Fn4 Z3Instance Z3Context Int Z3Sort Z3Ast

foreign import mk_string :: Fn4 Z3Instance Z3Context String Z3Sort Z3Ast

foreign import mk_true :: Fn2 Z3Instance Z3Context Z3Ast

foreign import mk_false :: Fn2 Z3Instance Z3Context Z3Ast

foreign import mk_not :: Fn3 Z3Instance Z3Context Z3Ast Z3Ast

foreign import mk_and :: Fn4 Z3Instance Z3Context Z3Ast Z3Ast Z3Ast

foreign import mk_add :: Fn4 Z3Instance Z3Context Z3Ast Z3Ast Z3Ast

foreign import mk_mul :: Fn4 Z3Instance Z3Context Z3Ast Z3Ast Z3Ast

foreign import mk_sub :: Fn4 Z3Instance Z3Context Z3Ast Z3Ast Z3Ast

foreign import mk_or :: Fn4 Z3Instance Z3Context Z3Ast Z3Ast Z3Ast

foreign import mk_eq :: Fn4 Z3Instance Z3Context Z3Ast Z3Ast Z3Ast

foreign import mk_lt :: Fn4 Z3Instance Z3Context Z3Ast Z3Ast Z3Ast

foreign import mk_le :: Fn4 Z3Instance Z3Context Z3Ast Z3Ast Z3Ast

foreign import mk_gt :: Fn4 Z3Instance Z3Context Z3Ast Z3Ast Z3Ast

foreign import mk_ge :: Fn4 Z3Instance Z3Context Z3Ast Z3Ast Z3Ast

foreign import solver_assert :: Fn4 Z3Instance Z3Context Z3Solver Z3Ast Unit

foreign import solver_get_model :: Fn3 Z3Instance Z3Context Z3Solver Z3Model

foreign import model_inc_ref :: Fn3 Z3Instance Z3Context Z3Model Unit

foreign import model_dec_rec :: Fn3 Z3Instance Z3Context Z3Model Unit

foreign import model_to_string :: Fn3 Z3Instance Z3Context Z3Model String

foreign import solver_check :: Fn3 Z3Instance Z3Context Z3Solver Int

foreign import ast_to_string :: Fn3 Z3Instance Z3Context Z3Ast String

foreign import func_decl_to_string :: Fn3 Z3Instance Z3Context Z3FuncDecl String

foreign import model_get_const_interp :: Fn4 Z3Instance Z3Context Z3Model Z3FuncDecl Z3Ast

foreign import mk_func_decl :: Fn4 Z3Instance Z3Context Z3Symbol Z3Sort Z3FuncDecl

foreign import mk_app :: Fn3 Z3Instance Z3Context Z3FuncDecl Z3Ast

foreign import solver_push :: Fn3 Z3Instance Z3Context Z3Solver Unit

foreign import solver_pop :: Fn3 Z3Instance Z3Context Z3Solver Unit

foreign import solver_inc_ref :: Fn3 Z3Instance Z3Context Z3Solver Unit

foreign import solver_dec_ref :: Fn3 Z3Instance Z3Context Z3Solver Unit
