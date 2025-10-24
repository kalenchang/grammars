module CFG where

import Prelude hiding ((^))
import Data.Tree
import Data.List (foldl')

import Printing
import Lambdas

data CFGRule nts ts = Branching {motherc :: nts, daughtersc :: [nts]} | Leafing {motherc :: nts, terms :: [ts]} deriving Eq
-- I think I want to keep terminals as [ts] solely because showing a single string is annoying...?

instance (Show nts, Show ts) => Show (CFGRule nts ts) where
    show (Branching a b) = show a ++ " ->" ++ insertSpaces b
    show (Leafing a b) = show a ++ " ->" ++ insertSpaces b

instance (Show nts) => Texable (CFGRule nts String) where
    texify (Branching a b) = show a ++ " \\ra{} " ++ insertSpaces b
    texify (Leafing a b) = show a ++ " \\ra{} " ++ stringSpaces b

-- rankc :: CFGRule nts ts -> Int
rankc (Leafing _ _) = 0
rankc (Branching _ b) = length b

data CFTree nts ts = CFT (CFGRule nts ts) [CFTree nts ts] deriving (Eq, Show)

categoryc :: (Eq nts) => CFTree nts ts -> Maybe nts
categoryc (CFT (Leafing a _) daughts) = if null daughts then Just a else Nothing
categoryc (CFT (Branching a b) daughts) = if and $ zipWith (\x -> \y -> Just x == categoryc y) b daughts 
                                            then Just a else Nothing

-- data Cats = CP | VP | NP | VE | VI | A | B | S deriving (Eq, Show)

cfg1r1 = Branching CP [NP, VP]
cfg1r2 = Branching VP [VI]
cfg1r3 = Branching VP [CP, VE]
cfg1r4m = Leafing NP ["Mary "]
cfg1r4j = Leafing NP ["John "]
cfg1r5l = Leafing VE ["let "]
cfg1r6r = Leafing VI ["run "]


mucfg1list = [(cfg1r1, lfa),
            (cfg1r2, idterm),
            (cfg1r3, lfa),
            (cfg1r4m, mary'),
            (cfg1r4j, john'),
            (cfg1r5l, let'),
            (cfg1r6r, run')]

mucfg1 = lookupint mucfg1list

-- cfg1t1 :: CFTree VN String
cfg1t1 = CFT cfg1r1 [
            CFT (cfg1r4m) [],
            CFT cfg1r3 [
                CFT cfg1r1 [
                    CFT (cfg1r4j) [],
                    CFT cfg1r2 [
                        CFT (cfg1r6r) []
                    ]
                ],
                CFT (cfg1r5l) []
            ]
        ]

cfg1t2 = CFT cfg1r3 [
                CFT cfg1r1 [
                    CFT (cfg1r4j) [],
                    CFT cfg1r2 [
                        CFT (cfg1r6r) []
                    ]
                ],
                CFT (cfg1r5l) []
            ]

-- yieldc :: Show ts => CFTree nts ts -> [ts]
yieldc (CFT (Leafing _ b) _) = b
yieldc (CFT (Branching _ _) daughters) = concat (map yieldc daughters)

cfgtoCatTree t@(CFT r ts) = Node (case categoryc t of {Just cat -> show cat; Nothing -> "n/a"}) (map cfgtoCatTree ts)

cfgtoBothTree t@(CFT r ts) = Node (catc ++ '\n': (concat (yieldc t))) (map cfgtoBothTree ts)
        where catc = case categoryc t of {Just cat -> show cat; Nothing -> "n/a"}

cfgtoThree t@(CFT r ts) = Node ((show r) ++ '\n':catc ++ ": " ++ (concat (yieldc t))) (map (cfgtoThree) ts)
        where catc = case categoryc t of {Just cat -> show cat; Nothing -> "n/a"}

denotec :: ((CFGRule nts ts) -> Term) -> (CFTree nts ts) -> Term
denotec mu (CFT r daughters) = foldl' (\x -> \y -> eval (Ap x y)) (mu r) (map (denotec mu) daughters)

cfgtoAllTree mu t@(CFT r ts) = Node ((show r) ++ '\n':catc ++ ": " ++ (concat (yieldc t)) ++ '\n':show (denotec mu t)) (map (cfgtoAllTree mu) ts)
        where catc = case categoryc t of {Just cat -> show cat; Nothing -> "n/a"}

cfgDerivedTree t@(CFT (Leafing a b) ts) = Node (show a) [Node (stringSpaces b) []]
cfgDerivedTree t@(CFT (Branching _ _) ts) = Node (case categoryc t of {Just cat -> show cat; Nothing -> "n/a"}) (map cfgDerivedTree ts)

-- cfgtoTexTree t@(CFT r ts) = Node ((texify r) ++ "\\" ++ )

-- can make a type for greibach rules/trees

cfg2r1 = Branching S [A, S, A]
cfg2r2 = Branching S [B, S, B]
cfg2r3 = Leafing A ["a"]
cfg2r4 = Leafing B ["b"]
cfg2r5 = Leafing S [""]

cfg2t1 = CFT cfg2r1 [
            CFT cfg2r3 [],
            CFT cfg2r1 [
                CFT cfg2r3 [],
                CFT cfg2r2 [
                    CFT cfg2r4 [],
                    CFT cfg2r5 [],
                    CFT cfg2r4 []
                ],
                CFT cfg2r3 []
            ],
            CFT cfg2r3 []
        ]