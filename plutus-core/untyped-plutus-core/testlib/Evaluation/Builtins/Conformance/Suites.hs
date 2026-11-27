-- | Registry of the builtin property suites that generate conformance cases.
module Evaluation.Builtins.Conformance.Suites
  ( Generator
  , Suite
  , allSuites
  ) where

import Evaluation.Builtins.Conformance
  ( CheckMode
  , OutputFormat
  , PropertyFilter
  , PropertyId
  , PropertyReport
  )

import Evaluation.Builtins.BLS12_381
  ( bls12_381_property_names
  , generate_bls12_381_properties
  )
import Evaluation.Builtins.Bitwise.CIP0122
  ( bitwise_cip0122_property_names
  , generate_bitwise_cip0122_properties
  )
import Evaluation.Builtins.Bitwise.CIP0123
  ( bitwise_cip0123_property_names
  , generate_bitwise_cip0123_properties
  )
import Evaluation.Builtins.Integer.DivModProperties
  ( generate_integer_div_mod_properties
  , integer_div_mod_property_names
  )
import Evaluation.Builtins.Integer.ExpModIntegerProperties
  ( generate_integer_exp_mod_properties
  , integer_exp_mod_property_names
  )
import Evaluation.Builtins.Integer.OrderProperties
  ( generate_integer_order_properties
  , integer_order_property_names
  )
import Evaluation.Builtins.Integer.QuotRemProperties
  ( generate_integer_quot_rem_properties
  , integer_quot_rem_property_names
  )
import Evaluation.Builtins.Integer.RingProperties
  ( generate_integer_ring_properties
  , integer_ring_property_names
  )

import Test.QuickCheck.Random (QCGen)

-- | Writes conformance cases for one suite, filtered by property.
type Generator =
  OutputFormat -> CheckMode -> PropertyFilter -> FilePath -> Int -> QCGen -> IO [PropertyReport]

-- | A suite's property identifiers together with the generator for its cases.
type Suite = ([PropertyId], Generator)

-- | Every suite that can generate conformance cases, in output order.
allSuites :: [Suite]
allSuites =
  [ (integer_ring_property_names, generate_integer_ring_properties)
  , (integer_div_mod_property_names, generate_integer_div_mod_properties)
  , (integer_quot_rem_property_names, generate_integer_quot_rem_properties)
  , (integer_order_property_names, generate_integer_order_properties)
  , (integer_exp_mod_property_names, generate_integer_exp_mod_properties)
  , (bitwise_cip0122_property_names, generate_bitwise_cip0122_properties)
  , (bitwise_cip0123_property_names, generate_bitwise_cip0123_properties)
  , (bls12_381_property_names, generate_bls12_381_properties)
  ]
