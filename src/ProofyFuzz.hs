
-- | Some built-in types
data Type = TInt | TReal | TClip | TClipNat | TBag Type
  deriving (Eq, Show)

-- | Right now, we can only handle a database or summing it.
data Expr = Arg | Sum Expr
  deriving (Eq, Show)

-- | A type synonym for pretty type signatures.
type Name = String

-- | The printT function prints the full type
printT TInt = "int"
printT TReal = "real"
printT TClip = "real"
printT TClipNat = "nat"
printT (TBag t) = "list "++printT t

-- | The printT' function prints only the top layer of the type
printT' TInt = "Int"
printT' TReal = "Real"
printT' TClip = "Real"
printT' TClipNat = "Nat"
printT' (TBag _) = "List"

-- | This is the main function.  This creates a lemma that will be 
--  sent to Coq to be checked.
makeLemma :: Name   -- ^ The name of the Lemma
          -> Type   -- ^ The type of the argument to the function
          -> Type   -- ^ The type of the rseult of the function
          -> Expr   -- ^ The body of the function
          -> String -- ^ The output lemma
makeLemma name targ tres e = 
    "Lemma "++name++" : forall (Arg Arg' : "++printT targ++"),\n"
  ++"sim"++printT' targ++" Arg Arg' ->\n"
  ++makePrecond "Arg"  targ++" ->\n"
  ++makePrecond "Arg'" targ++" ->\n"
  ++"sim"++printT' tres++" ("++makeExpr "Arg" e++") ("++makeExpr "Arg'" e++")."
  
-- | This function makes a precondition based on the argument type.
makePrecond :: Name -> Type -> String
makePrecond name TInt = "True"
makePrecond name TReal = "True"
makePrecond name TClip = "-1 <= "++name++" and "++name++" <= 1"
makePrecond name TClipNat = name++" <= 1"
makePrecond name (TBag t) = "all (fun x => "++makePrecond "x" t++") "++name

-- | This function creates a Coq version of the expression.
makeExpr :: Name -> Expr -> String
makeExpr arg Arg = arg
makeExpr arg (Sum e) = "sumList "++makeExpr arg e
