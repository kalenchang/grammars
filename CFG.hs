module CFG where

import Prelude
import TreePrint
import Data.Tree

data CFGRule nts ts = Branching {motherc :: nts, daughtersc :: [nts]} | Leafing {motherc :: nts, terms :: [ts]} deriving Eq

instance (Show nts, Show ts) => Show (CFGRule nts ts) where
    show (Branching a b) = show a ++ " ->" ++ insertSpaces b
    show (Leafing a b) = show a ++ " ->" ++ insertSpaces b

data CFTree nts ts = CFT (CFGRule nts ts) [CFTree nts ts] deriving (Eq, Show)

categoryc :: (Eq nts) => CFTree nts ts -> Maybe nts
categoryc (CFT (Leafing a _) daughts) = if null daughts then Just a else Nothing
categoryc (CFT (Branching a b) daughts) = if and $ zipWith (\x -> \y -> Just x == categoryc y) b daughts 
                                            then Just a else Nothing

data Cats = CP | VP | NP | VE | VI deriving (Eq, Show)

cfgr1 = Branching CP [NP, VP]
cfgr2 = Branching VP [VI]
cfgr3 = Branching VP [CP, VE]
-- cfgr4 :: ts -> CFGRule Cats ts
cfgr4 x = Leafing NP [x]
cfgr5 x = Leafing VE [x]
cfgr6 x = Leafing VI [x]

cfgt1 :: CFTree Cats String
cfgt1 = CFT cfgr1 [
            CFT (cfgr4 "Mary ") [],
            CFT cfgr3 [
                CFT cfgr1 [
                    CFT (cfgr4 "John ") [],
                    CFT cfgr2 [
                        CFT (cfgr6 "swim ") []
                    ]
                ],
                CFT (cfgr5 "saw ") []
            ]
        ]

-- yieldc :: Show ts => CFTree nts ts -> [ts]
yieldc (CFT (Leafing _ b) _) = b
yieldc (CFT (Branching _ _) daughters) = concat (map yieldc daughters)

cfgtoCatTree t@(CFT r ts) = Node (case categoryc t of {Just cat -> show cat; Nothing -> "n/a"}) (map cfgtoCatTree ts)

cfgtoBothTree t@(CFT r ts) = Node (cat ++ '\n': (concat (yieldc t))) (map cfgtoBothTree ts)
        where cat = case categoryc t of {Just cat -> show cat; Nothing -> "n/a"}
