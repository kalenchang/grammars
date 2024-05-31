module HGtoLIG where

import Prelude
import Data.Tree

data VN = S | T | B | C | D deriving (Eq, Show)

type VT = String

data HGRule = Concat {mother :: VN, lefts :: [VN], daughter :: VN, rights :: [VN], label :: Int} 
        | Wrap {mother :: VN, left :: VN, right :: VN, label :: Int}
        | Leaf {mother :: VN, lterms :: [VT], rterms :: [VT], label :: Int} deriving (Show, Eq)