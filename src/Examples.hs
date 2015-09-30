-----------------------------------------------------------------------------
-- |
-- Module      :  Examples
-- Copyright   :  (c) Daniel Winograd-Cort 2015
-- License     :  see the LICENSE file in the distribution
--
-- Maintainer  :  danwc@seas.upenn.edu
-- Stability   :  experimental
--
-- Example SFuzz functions

{-# LANGUAGE TemplateHaskell #-}
module Examples where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Types
import PMonad
import Syntax

mean :: ExpQ --P Int Int
mean = [| do
  s <- sumDB
  l <- countDB
  return (s / l) |]


cdf :: [Int] -> ExpQ --P Int [Int]
cdf buckets = case buckets of
  []    -> [| return [] |]
  (x:y) -> [| do
    cb <- splitDB (\n -> n < x)
            countDB
            $(cdf y)
    count  <- let (count,b) = cb in return count
    bigger <- let (c,bigger) = cb in return bigger
    return (count : bigger) |]


kmeans :: Int -> ExpQ --[(Int,Int)] -> ([(Int,Int)] -> P Int [(Int,Int)]) -> P Int [(Int,Int)]
kmeans iters = [|
  \centers iterate -> $(case iters of
    0 -> [| return centers |]
    n -> [| do
      nextCenters <- $(kmeans (n-1)) centers iterate
      return (iterate nextCenters) |]) |]


--idc :: Int -> ExpQ
--idc iter = [|
--  \qs pa dua evalQ -> $(case iter of
--    0 -> [| return [] |] -- The initial database approximation
--    n -> [| do
--      approx <- $(idc n) qs pa dua
--      q <- pa qs approx
--      actual <- return (evalQ 




