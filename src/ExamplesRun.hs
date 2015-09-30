
{-# LANGUAGE TemplateHaskell #-}
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Types
import PMonad
import Syntax
import Examples
import SFuzz

-- | A testing database.
testDB = [5,5,1,2,3,41,6,7,8,18,8,19]

--mean :: P Int Int
--mean = do
--  s <- sumDB
--  l <- countDB
--  return (s / l)

fuzz2 :: P Int Int
fuzz2 = do
  (fives,_) <- splitDB (==5) countDB (return ())
  return fives

test :: SFuzz r Int
test = do
  mean <- trustingFuzz 1 $(fuzzIt mean)
  exportVal $ show mean
  fives <- trustingFuzz 1 fuzz2
  exportVal $ show fives
  nums <- trustingFuzz 1 $(fuzzIt $ cdf [3, 6, 9, 40])
  exportVal $ show nums
  s <- trustingFuzz (fromIntegral fives) sumDB
  return s


mymain = runSFuzz test (createBudgetedDB testDB 5) id
