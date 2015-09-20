

module Syntax where


data VarInfo = VarInfo {
  -- Indexes start a 0
  v_index :: Int,

  -- Debug fields
  v_name  :: String,
  v_size  :: Int
}

data BinderInfo = BinderInfo {
  b_name :: String,
  b_size :: Int,    -- How many outside binders we had when this binded was found
  b_prim :: Bool
}

-- Primitive Terms
data PrimTerm = 
    PrimTUnit
  | PrimTNum Double
  | PrimTInt Int
  | PrimTBool Bool
  | PrimTString String
  | PrimTFun String
  | PrimTDBS String


data Term =
    TmVar VarInfo
  | TmPair Term Term
  --       (x,  y)
  | TmTensDest BinderInfo BinderInfo Term Term
  --       let (x,        y)       = t in e

  | TmUnionCase Term BinderInfo Term  BinderInfo Term
  --       case t of Left x  => tm1 | Right y => tm2

  -- Primitive terms
  | TmPrim     PrimTerm

  -- The three fundamental constructs of our language:
  --    Regular Abstraction and Applicacion
  | TmApp Term Term

  --    & constructor
  | TmAmpersand Term Term

