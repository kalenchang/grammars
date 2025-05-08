module CFG where

import Prelude
import TreePrint
import Data.Tree

data CFGRule nts ts = Branching {motherc :: nts, daughtersc :: [nts]} | Leafing {motherc :: nts, terms :: [ts]} deriving Eq
-- I think I want to keep terminals as [ts] solely because showing a single string is annoying...?

instance (Show nts, Show ts) => Show (CFGRule nts ts) where
    show (Branching a b) = show a ++ " ->" ++ insertSpaces b
    show (Leafing a b) = show a ++ " ->" ++ insertSpaces b

data CFTree nts ts = CFT (CFGRule nts ts) [CFTree nts ts] deriving (Eq, Show)

categoryc :: (Eq nts) => CFTree nts ts -> Maybe nts
categoryc (CFT (Leafing a _) daughts) = if null daughts then Just a else Nothing
categoryc (CFT (Branching a b) daughts) = if and $ zipWith (\x -> \y -> Just x == categoryc y) b daughts 
                                            then Just a else Nothing

data Cats = CP | VP | NP | VE | VI | AP | BP deriving (Eq, Show)

cfg1r1 = Branching CP [NP, VP]
cfg1r2 = Branching VP [VI]
cfg1r3 = Branching VP [CP, VE]
-- cfg1r4 :: ts -> CFGRule Cats ts
cfg1r4 x = Leafing NP [x]
cfg1r5 x = Leafing VE [x]
cfg1r6 x = Leafing VI [x]

cfg1t1 :: CFTree Cats String
cfg1t1 = CFT cfg1r1 [
            CFT (cfg1r4 "Mary ") [],
            CFT cfg1r3 [
                CFT cfg1r1 [
                    CFT (cfg1r4 "John ") [],
                    CFT cfg1r2 [
                        CFT (cfg1r6 "swim ") []
                    ]
                ],
                CFT (cfg1r5 "saw ") []
            ]
        ]

-- yieldc :: Show ts => CFTree nts ts -> [ts]
yieldc (CFT (Leafing _ b) _) = b
yieldc (CFT (Branching _ _) daughters) = concat (map yieldc daughters)

cfgtoCatTree t@(CFT r ts) = Node (case categoryc t of {Just cat -> show cat; Nothing -> "n/a"}) (map cfgtoCatTree ts)

cfgtoBothTree t@(CFT r ts) = Node (catc ++ '\n': (concat (yieldc t))) (map cfgtoBothTree ts)
        where catc = case categoryc t of {Just cat -> show cat; Nothing -> "n/a"}

cfgtoAllTree t@(CFT r ts) = Node ((show r) ++ '\n':catc ++ ": " ++ (concat (yieldc t))) (map cfgtoAllTree ts)
        where catc = case categoryc t of {Just cat -> show cat; Nothing -> "n/a"}

-- can make a type for greibach rules/trees

cfg2r1 = Branching CP [AP, CP, AP]
cfg2r2 = Branching CP [BP, CP, BP]
cfg2r3 = Leafing AP ["a"]
cfg2r4 = Leafing BP ["b"]
cfg2r5 = Leafing CP []

cfg2t1 = CFT cfg2r1 [
            CFT cfg2r3 [],
            CFT cfg2r2 [
                CFT cfg2r4 [],
                CFT cfg2r1 [
                    CFT cfg2r3 [],
                    CFT cfg2r5 [],
                    CFT cfg2r3 []
                ],
                CFT cfg2r4 []
            ],
            CFT cfg2r3 []
        ]