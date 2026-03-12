{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusIR.Core.Instance.Flat () where

import PlutusIR.Core.Type

import PlutusCore qualified as PLC
import PlutusCore.Flat (Flat (..))
import PlutusCore.Flat.Decoder.Prim (dBool)
import PlutusCore.Flat.Encoder (eBits16, eFalse, eTrue, (<>))
import PlutusCore.FlatInstances ()
import Prelude hiding ((<>))

{- Note [Serialization of PIR]
The serialized version of Plutus-IR will be included in the final
executable for helping debugging and testing and providing better error
reporting. It is not meant to be stored on the chain, which means that
the underlying representation can vary and backwards compatibility is
not required.
-}

-- | Recursivity: 2 constructors. NonRec=0, Rec=1.
instance Flat Recursivity where
  encode NonRec = eFalse
  encode Rec = eTrue
  decode = do
    tag <- dBool
    if tag then pure Rec else pure NonRec
  size _ n = 1 + n

-- | Strictness: 2 constructors. NonStrict=0, Strict=1.
instance Flat Strictness where
  encode NonStrict = eFalse
  encode Strict = eTrue
  decode = do
    tag <- dBool
    if tag then pure Strict else pure NonStrict
  size _ n = 1 + n

-- | Datatype: single constructor with 5 fields. No tag.
instance
  ( PLC.Closed uni
  , uni `PLC.Everywhere` Flat
  , Flat a
  , Flat tyname
  , Flat name
  )
  => Flat (Datatype tyname name uni a)
  where
  encode (Datatype a tvd tvds n vds) =
    encode a <> encode tvd <> encode tvds <> encode n <> encode vds
  decode = Datatype <$> decode <*> decode <*> decode <*> decode <*> decode
  size (Datatype a tvd tvds n vds) s =
    size a (size tvd (size tvds (size n (size vds s))))

{-| Binding: 3 constructors.
  Tree: TermBind=0, TypeBind=10, DatatypeBind=11 -}
instance
  ( PLC.Closed uni
  , uni `PLC.Everywhere` Flat
  , Flat fun
  , Flat a
  , Flat tyname
  , Flat name
  )
  => Flat (Binding tyname name uni fun a)
  where
  encode (TermBind a s vd t) = eFalse <> encode a <> encode s <> encode vd <> encode t
  encode (TypeBind a tvd ty) = eTrue <> eFalse <> encode a <> encode tvd <> encode ty
  encode (DatatypeBind a dt) = eTrue <> eTrue <> encode a <> encode dt
  decode = do
    tag <- dBool
    if tag
      then do
        tag2 <- dBool
        if tag2
          then DatatypeBind <$> decode <*> decode
          else TypeBind <$> decode <*> decode <*> decode
      else TermBind <$> decode <*> decode <*> decode <*> decode
  size (TermBind a s vd t) n = 1 + size a (size s (size vd (size t n)))
  size (TypeBind a tvd ty) n = 2 + size a (size tvd (size ty n))
  size (DatatypeBind a dt) n = 2 + size a (size dt n)

{-| Term: 13 constructors.
  Encoding (balanced binary tree, floor(n/2) left, ceil(n/2) right):
    Let      = 000  (3 bits)    Builtin  = 100  (3 bits)
    Var      = 0010 (4 bits)    TyInst   = 1010 (4 bits)
    TyAbs    = 0011 (4 bits)    Error    = 1011 (4 bits)
    LamAbs   = 010  (3 bits)    IWrap    = 1100 (4 bits)
    Apply    = 0110 (4 bits)    Unwrap   = 1101 (4 bits)
    Constant = 0111 (4 bits)    Constr   = 1110 (4 bits)
                                Case     = 1111 (4 bits) -}
instance
  ( PLC.Closed uni
  , uni `PLC.Everywhere` Flat
  , Flat fun
  , Flat a
  , Flat tyname
  , Flat name
  )
  => Flat (Term tyname name uni fun a)
  where
  encode (Let a r bs t) = eBits16 3 0 <> encode a <> encode r <> encode bs <> encode t
  encode (Var a n) = eBits16 4 2 <> encode a <> encode n
  encode (TyAbs a tn k t) = eBits16 4 3 <> encode a <> encode tn <> encode k <> encode t
  encode (LamAbs a n ty t) = eBits16 3 2 <> encode a <> encode n <> encode ty <> encode t
  encode (Apply a t1 t2) = eBits16 4 6 <> encode a <> encode t1 <> encode t2
  encode (Constant a c) = eBits16 4 7 <> encode a <> encode c
  encode (Builtin a f) = eBits16 3 4 <> encode a <> encode f
  encode (TyInst a t ty) = eBits16 4 10 <> encode a <> encode t <> encode ty
  encode (Error a ty) = eBits16 4 11 <> encode a <> encode ty
  encode (IWrap a ty1 ty2 t) = eBits16 4 12 <> encode a <> encode ty1 <> encode ty2 <> encode t
  encode (Unwrap a t) = eBits16 4 13 <> encode a <> encode t
  encode (Constr a ty i ts) = eBits16 4 14 <> encode a <> encode ty <> encode i <> encode ts
  encode (Case a ty t ts) = eBits16 4 15 <> encode a <> encode ty <> encode t <> encode ts
  decode = do
    b0 <- dBool
    if not b0
      then do
        -- left 6: Let, Var, TyAbs, LamAbs, Apply, Constant
        b1 <- dBool
        if not b1
          then do
            -- left 3: Let, Var, TyAbs
            b2 <- dBool
            if not b2
              then Let <$> decode <*> decode <*> decode <*> decode
              else do
                b3 <- dBool
                if not b3
                  then Var <$> decode <*> decode
                  else TyAbs <$> decode <*> decode <*> decode <*> decode
          else do
            -- right 3: LamAbs, Apply, Constant
            b2 <- dBool
            if not b2
              then LamAbs <$> decode <*> decode <*> decode <*> decode
              else do
                b3 <- dBool
                if not b3
                  then Apply <$> decode <*> decode <*> decode
                  else Constant <$> decode <*> decode
      else do
        -- right 7: Builtin, TyInst, Error, IWrap, Unwrap, Constr, Case
        b1 <- dBool
        if not b1
          then do
            -- left 3: Builtin, TyInst, Error
            b2 <- dBool
            if not b2
              then Builtin <$> decode <*> decode
              else do
                b3 <- dBool
                if not b3
                  then TyInst <$> decode <*> decode <*> decode
                  else Error <$> decode <*> decode
          else do
            -- right 4: IWrap, Unwrap, Constr, Case
            b2 <- dBool
            if not b2
              then do
                b3 <- dBool
                if not b3
                  then IWrap <$> decode <*> decode <*> decode <*> decode
                  else Unwrap <$> decode <*> decode
              else do
                b3 <- dBool
                if not b3
                  then Constr <$> decode <*> decode <*> decode <*> decode
                  else Case <$> decode <*> decode <*> decode <*> decode
  size (Let a r bs t) n = 3 + size a (size r (size bs (size t n)))
  size (Var a nm) n = 4 + size a (size nm n)
  size (TyAbs a tn k t) n = 4 + size a (size tn (size k (size t n)))
  size (LamAbs a nm ty t) n = 3 + size a (size nm (size ty (size t n)))
  size (Apply a t1 t2) n = 4 + size a (size t1 (size t2 n))
  size (Constant a c) n = 4 + size a (size c n)
  size (Builtin a f) n = 3 + size a (size f n)
  size (TyInst a t ty) n = 4 + size a (size t (size ty n))
  size (Error a ty) n = 4 + size a (size ty n)
  size (IWrap a ty1 ty2 t) n = 4 + size a (size ty1 (size ty2 (size t n)))
  size (Unwrap a t) n = 4 + size a (size t n)
  size (Constr a ty i ts) n = 4 + size a (size ty (size i (size ts n)))
  size (Case a ty t ts) n = 4 + size a (size ty (size t (size ts n)))

-- | Program: single constructor (record) with 3 fields. No tag.
instance
  ( PLC.Closed uni
  , uni `PLC.Everywhere` Flat
  , Flat fun
  , Flat a
  , Flat tyname
  , Flat name
  )
  => Flat (Program tyname name uni fun a)
  where
  encode (Program a v t) = encode a <> encode v <> encode t
  decode = Program <$> decode <*> decode <*> decode
  size (Program a v t) n = size a (size v (size t n))
