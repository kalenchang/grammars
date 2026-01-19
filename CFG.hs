module CFG where

import Prelude hiding ((^))
import Data.Tree
import Data.List (foldl')
import Control.Monad

import Printing
import Lambdas

data CFGRule nts ts = Branching {motherc :: nts, daughtersc :: [nts]} | Leafing {motherc :: nts, terms :: [ts]} deriving Eq
-- I think I want to keep terminals as [ts] solely because showing a single string is annoying...?

instance (Show nts, Show ts) => Show (CFGRule nts ts) where
    show (Branching a b) = show a ++ " ->" ++ insertSpaces b
    show (Leafing a b) = show a ++ " ->" ++ insertSpaces b

instance (Texable nts) => Texable (CFGRule nts String) where
    texify (Branching a b) = texify a ++ " \\ra{} " ++ texifySpaces b
    texify (Leafing a b) = texify a ++ " \\ra{} " ++ stringSpaces b

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

cfgtoThreeLatex t@(CFT r ts) = Node ((texify r) ++ "\\\\" ++ catc ++ ": " ++ (concat (yieldc t))) (map (cfgtoThreeLatex) ts)
        where catc = case categoryc t of {Just cat -> texify cat; Nothing -> "n/a"}

-- need to clean this up... should prob create a data structure to be at each node, such as "cat" or "cat+yield" or "cat+yield+rule" or "rule+cat+yield+denote", etc
-- these will just be triples or tuples or whatever, and they will have instances for show and texify
-- that way i can just show/texify these trees directly

denotec :: ((CFGRule nts ts) -> Term) -> (CFTree nts ts) -> Term
denotec mu (CFT r daughters) = foldl' (\x -> \y -> eval (Ap x y)) (mu r) (map (denotec mu) daughters)

cfgtoAllTree mu t@(CFT r ts) = Node ((show r) ++ '\n':catc ++ ": " ++ (concat (yieldc t)) ++ '\n':show (denotec mu t)) (map (cfgtoAllTree mu) ts)
        where catc = case categoryc t of {Just cat -> show cat; Nothing -> "n/a"}

cfgtoAllLatex mu t@(CFT r ts) = Node ((texify r) ++ "\\\\" ++ catc ++ ": " ++ (concat (yieldc t)) ++ "\\\\" ++ texify (denotec mu t)) (map (cfgtoAllLatex mu) ts)
        where catc = case categoryc t of {Just cat -> texify cat; Nothing -> "n/a"}

cfgtoDenLatex mu t@(CFT r ts) = Node ((texify r) ++ "\\\\" ++ texify (denotec mu t)) (map (cfgtoDenLatex mu) ts)

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


-- cfg3: arithmetic expressions
cfg3r1 = Branching S [S, R, S]
cfg3r2 = Leafing N ["1"]
cfg3r3 = Leafing N ["2"]
cfg3r4 = Leafing N ["3"]
cfg3r5 = Leafing R ["+"]
cfg3r6 = Leafing R ["x"]
cfg3r7 = Branching S [N]

cfg3t1 = CFT cfg3r1 [
            CFT cfg3r1 [
                CFT cfg3r7 [CFT cfg3r3 []],
                CFT cfg3r6 [],
                CFT cfg3r1 [
                    CFT cfg3r7 [CFT cfg3r3 []],
                    CFT cfg3r5 [],
                    CFT cfg3r7 [CFT cfg3r4 []]
                ]
            ],
            CFT cfg3r5 [],
            CFT cfg3r7 [CFT cfg3r2 []]
        ]

mucfg3list = [(cfg3r1, binop),
            (cfg3r2, n1'),
            (cfg3r3, n2'),
            (cfg3r4, n3'),
            (cfg3r5, plus'),
            (cfg3r6, times'),
            (cfg3r7, idterm)]

mucfg3 = lookupint mucfg3list

-- LEFT RECURSION ELIMINATION

-- 0 for original categories, 1 for primed categories, 2 for terminal categories
-- new version: 2 no longer exists; just assume the source grammar has no rules of L -> a, where L in elims (left recursion cat)
lre :: (Monoid ts, Eq nts) => [nts] -> CFTree nts ts -> CFTree (nts, Int) ts
lre _ (CFT (Leafing a [b]) []) = CFT (Leafing (a,0) [b]) []
lre elims (CFT (Branching a blist@(b:bs)) dlist@(dl:ds))
    | a `elem` elims && a == b = lre' elims dl (CFT (Branching (a,1) $ (map (,0) bs)++[(a,1)]) $ (map (lre elims) ds)++[CFT (Leafing (a,1) [mempty]) []])
    | a `elem` elims = CFT (Branching (a,0) $ (map (,0) blist)++[(a,1)]) $ (map (lre elims) dlist)++[CFT (Leafing (a,1) [mempty]) []]
    | otherwise = CFT (Branching (a,0) (map (,0) blist)) $ map (lre elims) dlist

-- presently, assume that L does not have any leaf rules
lre' :: (Monoid ts, Eq nts) => [nts] -> CFTree nts ts -> CFTree (nts, Int) ts ->  CFTree (nts, Int) ts
-- lre' elims (CFT (Leafing a [b]) []) dr = CFT (Branching (a,0) [(a,2),(a,1)]) [CFT (Leafing (a,2) [b]) [],dr]
lre' elims (CFT (Branching a blist@(b:bs)) dlist@(dl:ds)) dr
    | a == b = lre' elims dl (CFT (Branching (a,1) $ (map (,0) bs)++[(a,1)]) $ (map (lre elims) ds) ++ [dr])
    | otherwise = CFT (Branching (a,0) $ (map (,0) blist)++[(a,1)]) $ (map (lre elims) dlist) ++ [dr]

lremu elims (Leafing a [b], int) = (Leafing (a,0) [b], int)
lremu elims (Branching a blist@(b:bs), int)
    | a `elem` elims && a == b = (Branching (a,1) $ (map (,0) bs)++[(a,1)], lreloop (length bs) # int)
    | a `elem` elims = (Branching (a,0) $ (map (,0) blist)++[(a,1)], lreend (length blist) # int)
    | otherwise = (Branching (a,0) (map (,0) blist), int)


makemulre elims mulist = lookupint (map (lremu elims) mulist ++ 
                                    map (\x -> (Leafing (x,1) [mempty], idterm)) elims) -- ++ 
                                    -- map (\x -> (Branching (x,0) [(x,2),(x,1)], lfa)) elims

-- don't know why, but Haskell assumes it's (VN, Integer) unless I specify Int...
mucfg3' :: CFGRule (VN, Int) String -> Term
mucfg3' = makemulre [S] mucfg3list
