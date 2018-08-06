/*

data TermF r
  = Decname (Sourced String) [Type]
  | Let r r
  | Lam Type r
  | App r r
  | Con String [r]
  | Case [r] [ClauseF r]
  | Success r
  | Failure Type
  | Bind r r
  | PrimData PrimData
  | Builtin String [r]
  deriving (Functor,Foldable,Traversable,Generic)

*/

Data.Alts( "Decname",
           "Let",
           "Lam",
           "App",
           "Con",
           "Case",
           "Success",
           "Failure",
           "Bind",
           "PrimData",
           "Builtin" );





/*

data PrimData = PrimInt Int
              | PrimFloat Float
              | PrimByteString BS.ByteString
  deriving (Eq,Generic)

*/

Data.Alts( "PrimInt",
           "PrimFloat",
           "PrimByteString" );





/*

data ClauseF r = Clause [Scope PatternF] r
  deriving (Functor,Foldable,Traversable,Generic)

*/

Data.Alts( "Clause" );





/*

data PatternF r = ConPat String [r]
                | PrimPat PrimData
  deriving (Functor,Foldable,Traversable,Generic)

*/

Data.Alts( "VarPat",
           "ConPat",
           "PrimPat" );
