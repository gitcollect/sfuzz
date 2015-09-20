-----------------------------------------------------------------------------
-- |
-- Module      :  SFuzz
-- Copyright   :  (c) Daniel Winograd-Cort 2015
-- License     :  see the LICENSE file in the distribution
--
-- Maintainer  :  danwc@seas.upenn.edu
-- Stability   :  experimental
--
-- A staged version of the Fuzz language, originally built at UPenn.

{-# LANGUAGE TemplateHaskell, RankNTypes #-}

module SFuzz (
  Database, Epsilon,
  BudgetedDB,
  SFuzz, exportVal,
  trustingFuzz
) where

--import Language.Haskell.TH.Syntax
import Control.Monad (ap)
import Control.Applicative

-- | I am arbitrarily setting that a Database is a list of ints.
type Database = [Int]

-- | The epsilon value for privacy budget is a Double.
type Epsilon = Double

-- | A database along with its privacy budget.
newtype BudgetedDB = BudgetedDB (Database, Epsilon)

-- | The constructor/destructor for BudgetedDB is not exported, so we 
--  provide a smart constructor for it.
createBudgetedDB :: Database -> Epsilon -> BudgetedDB
createBudgetedDB = curry BudgetedDB

-- | The function takes a budgeted database and an operation with 
--  associated epsilon use, and, if the database can handle this much 
--  epsilon, it returns the result.  Otherwise, it returns Nothing.
useDB :: BudgetedDB -> (Epsilon, Database -> a) -> Maybe a
useDB (BudgetedDB (db, budget)) (eps, op) = if budget-eps < 0 then Nothing else Just (op db)

-- Subtract the given amount of Epsilon from the budgeted DB.
subtractEpsilon :: Epsilon -> BudgetedDB -> BudgetedDB
subtractEpsilon eps (BudgetedDB (db, budget)) = BudgetedDB (db, budget-eps)

-- | This is the main type for staged fuzz.  It is the monad in which we 
--  build our staged computations.  It is essentially a combination of 
--  a writer monad for [String], a continuation monad, an error monad, 
--  and sort of a state monad (with the BudgetedDB and Epsilon).  
--  There are three main forms of SFuzz computations.
--
--  - Pure computations (with return).
--
--  - Exporting values to save them for output.
--
--  - Running Fuzz computations.
data SFuzz r a = SFuzz { runSFuzz :: BudgetedDB -> ((Epsilon, [String], Maybe a) -> r) -> r }

instance Functor (SFuzz r) where
  fmap f (SFuzz g) = SFuzz h where
    h db k = g db k' where
      k' (e, strs, a) = k (e, strs, fmap f a)

instance Applicative (SFuzz r) where
  pure = return
  (<*>) = ap

instance Monad (SFuzz r) where
  return a = SFuzz $ \_ k -> k (0, [], Just a)
  g >>= f = SFuzz $ \db k ->
    runSFuzz g db $ \(e, strs, a) -> case a of
      Nothing -> k (e, strs, Nothing)
      Just a' -> runSFuzz (f a') (subtractEpsilon e db) $ \(e', strs', b) ->
        k (e+e', strs++strs', b)

-- | An entire SFuzz computation may fail, but even so, a portion of it 
--  may succeed.  To allow one to save partial results of computations, 
--  one can use the exportVal function.
exportVal :: String -> SFuzz r ()
exportVal s = SFuzz $ \_ k -> k (0, [s], Just ())

-- | The trustingFuzz function is an entirely unsafe Fuzz function that 
--  asks for a computation using the database and the amount of epsilon 
--  that computation uses and trusts the caller that this epsilon is 
--  correct.
trustingFuzz :: Epsilon -> (Database -> a) -> SFuzz r a
trustingFuzz eps op = SFuzz $ \db k ->
    k (eps, [], useDB db (eps, op))

-- | A testing database.
testDB = [5,1,2,3,4,5,5,6,7,8,8,8,9]

test :: SFuzz r Int
test = do
  mean <- trustingFuzz 1 (\db -> sum db `div` length db)
  exportVal $ show mean
  hd <- trustingFuzz 1 head
  exportVal $ show hd
  s <- trustingFuzz (fromIntegral hd) sum
  return s

main = runSFuzz test (createBudgetedDB testDB 5) id



