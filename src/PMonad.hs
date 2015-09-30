-----------------------------------------------------------------------------
-- |
-- Module      :  PMonad
-- Copyright   :  (c) Daniel Winograd-Cort 2015
-- License     :  see the LICENSE file in the distribution
--
-- Maintainer  :  danwc@seas.upenn.edu
-- Stability   :  experimental
--
-- The definition and simple functions of the Probability (and database)
--  monad.

module PMonad where

import Control.Monad (ap)
import Control.Applicative
import Data.List (partition)

import Types


-- | The probability monad for StagedFuzz is a little more complex than 
--  that for previous version of Fuzz because we build the database into 
--  it directly.
--  FIXME: It currently doesn't do any probability.
data P db a = P { runProb :: Database db -> a }

instance Functor (P db) where
  fmap f (P g) = P (f . g)

instance Applicative (P db) where
  pure = return
  (<*>) = ap

instance Monad (P db) where
  return a = P $ \_ -> a
  g >>= f = P $ \db -> runProb (f (runProb g db)) db

-- | Count the elements in a database returning its fuzzed size.
countDB :: P b Int
countDB = P length

-- | Sum the elements in a database returning its fuzzed sum.
sumDB :: Num n => P n n
sumDB = P sum

-- | Map a function over the elements of a database and apply the given 
--  monadic computation to the modified database.
mapDB :: (b -> c) -> P c a -> P b a
mapDB f (P g) = P h where
  h db = g $ map f db

-- | Split a database based on a filtering function.  Apply the first 
--  computation to the True portion and the second computation to the 
--  False portion and then pair the results together.
splitDB :: (c -> Bool) -> P c a -> P c b -> P c (a,b)
splitDB p (P f) (P g) = P h where
  h db = let (dbt,dbf) = partition p db in (f dbt, g dbf)





