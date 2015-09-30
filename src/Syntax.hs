
{-# LANGUAGE TemplateHaskell #-}
module Syntax (fuzzIt) where

import Types

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

{-
Basic type checking should be easy and built in at the actual type level.
That is, variables and functions etc. should be marked with their type.
Thus, primitive type checking is performed entirely statically, but 
Fuzz type checking (checking Epsilon) is performed dynamically when 
necessary.

I'll need to make a data type for Types, and then every term will need 
to be annotated by those types.  They may need to be GADTs.
... At that point, I'll need type variables or type inference or something.

Another thing to do is to make a quasiquoter and allow direct parsing.  
I'm not sure if this is really necessary though.

-}

-- | The information about a variable.  Currently, we only care about 
--  the name
data VarInfo = VarInfo {
--    v_index :: Int,       -- ^ Indexes start a 0
--    v_size  :: Int,       -- ^ (Debug field) The size(?) of the variable
    v_name  :: String     -- ^ (Debug field) The name of the variable
  }
  deriving Show

-- | The information about a pattern binding.  Currently, we only care 
-- about the name
data PatternInfo = PatternInfo {
--    p_size :: Int,    -- ^ How many outside binders we had when this binder was found
--    p_prim :: Bool,   -- ^ Note sure ...
    p_name :: String  -- ^ The name of the pattern variable(?)
  }
  deriving Show

-- | These are the primitive terms of the Fuzz language.
data PrimTerm = 
    PrimTUnit           -- ^ Unit ()
  | PrimEmptyList       -- ^ Empty list []
  | PrimTNum Double     -- ^ A floating point number
  | PrimTInt Int        -- ^ An integer
  | PrimTBool Bool      -- ^ A Boolean
  | PrimTString String  -- ^ A String
  | PrimTFun PrimFun    -- ^ A built-in function
  | PrimTCon PrimCon    -- ^ A built-in constructor
  deriving Show

-- | These are the built-in functions of the Fuzz language.
data PrimFun = 
    PrimFAdd        -- ^ Curried Addition
  | PrimFSub        -- ^ Curried Subtraction
  | PrimFMul        -- ^ Curried Multiplication
  | PrimFDiv        -- ^ Curried Division
  | PrimFStrConcat  -- ^ Curried String concatenation
  | PrimFReturn     -- ^ Monadic return
  | PrimFLT         -- ^ Curried less-than function
  deriving Show

-- | These are the built-in constructors of the Fuzz language.
data PrimCon = 
    PrimCLeft       -- ^ Left injection into sum type
  | PrimCRight      -- ^ Right injection into sum type
  | PrimCCons       -- ^ List construction
  deriving Show

-- | A term is the main component of a Fuzz computation.
data Term =
    TmVar VarInfo       -- ^ A variable with some variable information
  | TmPair Term Term    -- ^ A pair of two terms (e1,e2)
  | TmPairProj PatternInfo PatternInfo Term Term
    -- ^ Projection of a product type (pair) expressed as a let binding.  
    --  That is, a term of the form (TmPairProj x y t e) will be 
    --  decomposed into: let (x, y) = t in e
  | TmUnionCase Term PatternInfo Term PatternInfo Term
    -- ^ Projection of a sum type, otherwise known as a case expression.  
    --  That is, a term of the form (TmUnionCase e x e1 y e2) will be 
    --  decomposed into: case e of Left x  => e1 | Right y => e2
  | TmPrim PrimTerm     -- ^ A primitive term.
  | TmCond Term Term Term   -- ^ A conditional statement.

  | TmApp Term Term     -- ^ Expression application
  | TmAbs PatternInfo Term  -- ^ Lambda abstraction
  
  | TmBind Term PatternInfo Term
  deriving Show


-----------------------------------------------------------------------
-- Using Fuzz
-----------------------------------------------------------------------
-- | We can fuzz a template haskell exp by applying 'fuzzIt' to it.  
--  The ExpQ is parsed and then evaluated.  In the future, this will 
--  also type check and find the Epsilon value.
--  Typical application will look like:
--      $(fuzzIt fuzzFun)
--  where fuzzFun is an ExpQ Fuzz function.
fuzzIt qexp = qexp >>= (return . parseTerm) >>= evalTerm


-----------------------------------------------------------------------
-- Type checking Fuzz terms
-----------------------------------------------------------------------

-- | This will be the type checker.  I'm hoping I can use Haskell's 
--  type system as much as possible to make this simple.  Ideally, I'll 
--  only need it for the actual Fuzz part of type checking (i.e. 
--  epsilon), but seeing as how I haven't written it yet, we'll see.
typeCheck :: Term -> Epsilon
typeCheck t = error "Not implemented yet"

-----------------------------------------------------------------------
-- Evaluating Fuzz terms
-----------------------------------------------------------------------

-- | Rather than do environments and scoping myself, I leave it all to 
--  native Haskell.  Thus, evaluating a Fuzz expression is really just 
--  the act of converting it to a ExpQ so that we can splice it into 
--  the program where we want it.
evalTerm :: Term -> ExpQ
evalTerm (TmVar vi) = varE $ mkName (v_name vi)
evalTerm (TmPair t1 t2) = tupE [evalTerm t1, evalTerm t2]
evalTerm (TmPairProj x y t e) = appE (lamE [tupP [evalPat x, evalPat y]] (evalTerm e))
                                     (evalTerm t)
evalTerm (TmUnionCase e x e1 y e2) = caseE (evalTerm e)
    [match (conP (mkName "Left") [evalPat x]) (normalB $ evalTerm e1) [],
     match (conP (mkName "Right") [evalPat y]) (normalB $ evalTerm e2) []]
evalTerm (TmCond b t e) = condE (evalTerm b) (evalTerm t) (evalTerm e)
evalTerm (TmApp f x) = appE (evalTerm f) (evalTerm x)
evalTerm (TmAbs x e) = lamE [evalPat x] (evalTerm e)
evalTerm (TmPrim prim) = evalPrim prim
evalTerm (TmBind e1 x e2) = infixE (Just $ evalTerm e1)
    [| (>>=) |] (Just $ lamE [evalPat x] (evalTerm e2))

-- | Evaluating Fuzz patterns likewise converts them to PatQ values.
evalPat :: PatternInfo -> PatQ
evalPat = varP . mkName . p_name

-- | We evaluate Fuzz primitives to ExpQ.
evalPrim :: PrimTerm -> ExpQ
evalPrim PrimTUnit = [| () |]
evalPrim PrimEmptyList = [| [] |]
evalPrim (PrimTNum n) = litE $ RationalL $ toRational n
evalPrim (PrimTInt n) = [| n |]
evalPrim (PrimTBool b) = [| b |]
evalPrim (PrimTString s) = [| s |]
evalPrim (PrimTFun f) = evalPrimFun f
evalPrim (PrimTCon c) = evalPrimCon c

-- | We evaluate Fuzz primitive functions to ExpQ.
evalPrimFun :: PrimFun -> ExpQ
evalPrimFun PrimFAdd = [| (+) |]
evalPrimFun PrimFSub = [| (-) |]
evalPrimFun PrimFMul = [| (*) |]
evalPrimFun PrimFDiv = [| div |]
evalPrimFun PrimFStrConcat = [| (++) |]
evalPrimFun PrimFReturn = [| return |]
evalPrimFun PrimFLT = [| (<) |]

-- | We evaluate Fuzz primitive constructors to ExpQ.
evalPrimCon :: PrimCon -> ExpQ
evalPrimCon PrimCLeft = [| Left |]
evalPrimCon PrimCRight = [| Right |]
evalPrimCon PrimCCons = [| (:) |]


-----------------------------------------------------------------------
-- Parsing Fuzz terms
-----------------------------------------------------------------------

-- | This is the proto-quasiquoter for Fuzz.  Rather than do real actual 
--  parsing, it takes a Template Haskell Exp and turns it into a Fuzz 
--  term.  This feels pretty ad-hoc, but it works for now.
parseTerm :: Exp -> Term
parseTerm (VarE nm@(Name (OccName s) _)) = case s of
    "+" -> TmPrim (PrimTFun PrimFAdd)
    "-" -> TmPrim (PrimTFun PrimFSub)
    "*" -> TmPrim (PrimTFun PrimFMul)
    "/" -> TmPrim (PrimTFun PrimFDiv)
    "++" -> TmPrim (PrimTFun PrimFStrConcat)
    "return" -> TmPrim (PrimTFun PrimFReturn)
    "<" -> TmPrim (PrimTFun PrimFLT)
    _ -> TmVar (VarInfo $ show nm)
parseTerm (ConE nm@(Name (OccName s) _)) = case s of
    "Left" -> TmPrim (PrimTCon (PrimCLeft))
    "Right" -> TmPrim (PrimTCon (PrimCRight))
    ":" -> TmPrim (PrimTCon (PrimCCons))
    "True" -> TmPrim (PrimTBool True)
    "False" -> TmPrim (PrimTBool False)
    "()" -> TmPrim PrimTUnit
    _ -> error $ "Unsupported Constructor: " ++ show nm
parseTerm (ListE []) = TmPrim PrimEmptyList
parseTerm (LitE lit) = case lit of
    StringL s -> TmPrim (PrimTString s)
    IntegerL i -> TmPrim (PrimTInt (fromInteger i))
    RationalL r -> TmPrim (PrimTNum (fromRational r))
    _ -> error $ "Unsupported literal: " ++ show lit
parseTerm (AppE e1 e2) = TmApp (parseTerm e1) (parseTerm e2)
parseTerm (InfixE me1 op me2) = case (me1,me2) of
    (Nothing, Nothing) -> parseTerm op
    (Just e1, Nothing) -> TmApp (parseTerm op) (parseTerm e1)
    (Nothing, Just e2) -> error $ "Unsupported section"
    (Just e1, Just e2) -> TmApp (TmApp (parseTerm op) (parseTerm e1)) (parseTerm e2)
parseTerm (ParensE e) = parseTerm e
parseTerm (LamE [p] e) = TmAbs (parsePattern p) (parseTerm e)
parseTerm (LamE (p:ps) e) = TmAbs (parsePattern p) (parseTerm (LamE ps e))
parseTerm (TupE [e1,e2]) = TmPair (parseTerm e1) (parseTerm e2)
parseTerm (CondE b t e) = TmCond (parseTerm b) (parseTerm t) (parseTerm e)
parseTerm (LetE [ValD (TupP [x,y]) (NormalB t) []] e) = 
    TmPairProj (parsePattern x) (parsePattern y) (parseTerm t) (parseTerm e)
parseTerm t@(CaseE e [Match (ConP (Name (OccName l) _) [x]) (NormalB e1) [], 
                      Match (ConP (Name (OccName r) _) [y]) (NormalB e2) []]) = 
  if (l == "Left" && r == "Right")
  then TmUnionCase (parseTerm e) (parsePattern x) (parseTerm e1) (parsePattern y) (parseTerm e2)
  else error $ "Unsupported term: " ++ show t
parseTerm (DoE [NoBindS e]) = parseTerm e
parseTerm (DoE [s]) = error $ "The last statement in a 'do' block must be an expression, but given: "
    ++ show s
parseTerm (DoE (s:stmts)) = case s of
  BindS p e -> TmBind (parseTerm e) (parsePattern p) (parseTerm (DoE stmts))
  _ -> error $ "Unsupported statement: " ++ show s
parseTerm e = error $ "Unsupported term: " ++ show e

-- | This is a helper function for 'parseTerm' which parses patterns.
parsePattern :: Pat -> PatternInfo
parsePattern (VarP n) = PatternInfo $ show n
parsePattern p = error $ "Unsupported Pattern: " ++ show p




    

