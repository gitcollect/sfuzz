-----------------------------------------------------------------------------
-- |
-- Module      :  Types
-- Copyright   :  (c) Daniel Winograd-Cort 2015
-- License     :  see the LICENSE file in the distribution
--
-- Maintainer  :  danwc@seas.upenn.edu
-- Stability   :  experimental
--
-- Base types for SFuzz.

module Types (
  Database, Epsilon
) where

-- | I am arbitrarily setting that a Database is a list of ints.
type Database db = [db]

-- | The epsilon value for privacy budget is a Double.
type Epsilon = Double
