{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use const" #-}
{-# HLINT ignore "Use concatMap" #-}
{-# HLINT ignore "Redundant bracket" #-}
module LIGtoHG where

import Prelude
import Data.Maybe ( isJust, fromJust )
import Data.Tree

-- nonterminals; Vt = transitive verb, Ve = embedding verb, Tr = trace
data VN = S | T | U | A | B | C | D deriving (Show, Eq)

-- terminals
type VT = String

-- indices
type VI = Integer

-- stack change
data SC = NoChange | Push VI | Pop VI deriving (Show, Eq)

-- two kinds of LIG rules: Branch node or a Leaf node
-- Branch: 1 rewrites as 2 3 4, where 3 is the distinguished daughter, with stack change 5
-- Leaf: 1 rewrites as 2
-- data LIGRule = Branch VN [VN] VN [VN] SC Int | Leaf VN [VT] Int deriving (Show, Eq)
data LIGRule = Branch {mother :: VN, lefts :: [VN], daughter :: VN, rights :: [VN], change :: SC, label :: Int} 
        | Leaf {mother :: VN, terms :: [VT], label :: Int} deriving (Show, Eq)

newtype LIG = LIG ([VN], [VT], [VI], VN, [LIGRule])

-- instance Show LIGRule where
--     show (Branch _ _ _ _ _ x) = "rule" ++ (show x)

-- TODO: add record types
-- list of rules
ligr1, ligr2, ligr3, ligr4, ligr5, ligr6, ligr7, ligr8, ligr9, ligr10, ligr0 :: LIGRule
ligr1 = Branch S [A] S [] (Push 1) 1
ligr2 = Branch S [] T [] NoChange 2 
ligr3 = Branch T [B] T [D] NoChange 3
ligr4 = Branch T [] U [] NoChange 4
ligr5 = Branch U [] U [C] (Pop 1) 5
ligr6 = Leaf U [""] 6
ligr7 = Leaf A ["a"] 7
ligr8 = Leaf B ["b"] 8
ligr9 = Leaf C ["c"] 9
ligr10 = Leaf D ["d"] 10
-- dummy rule
ligr0 = Branch S [] T [] NoChange 0

ligrlist :: [LIGRule]
ligrlist = [ligr1, ligr2, ligr3, ligr4, ligr5, ligr6, ligr7, ligr8, ligr9, ligr10]

lookupLIGR :: Int -> [LIGRule] -> LIGRule
lookupLIGR n (x:xs) = if label x == n then x else lookupLIGR n xs
lookupLIGR _ [] = ligr0

getrule :: Int -> LIGRule
getrule x = lookupLIGR x ligrlist

-- show ligr1 = "r1"

data LITree = LIT LIGRule [LITree] deriving (Show, Eq)

changeStack :: SC -> Maybe [VI] -> Maybe [VI]
changeStack _ Nothing = Nothing
changeStack NoChange s = s
changeStack (Push i) (Just s) = Just (i:s)
changeStack (Pop i) (Just []) = Nothing
changeStack (Pop i) (Just (x:s)) = if x == i then Just s else Nothing

stackLister :: [a] -> [a] -> [VI] -> [[VI]]
stackLister l r s = map (\x -> []) l ++ s:(map (\x -> []) r)

-- check whether a tree produces the given category
-- still need to check whether stack clears
produces :: LITree -> VN -> [VI] -> Bool
produces (LIT (Branch a b c d e _) daughters) nt stack = let newStack = changeStack e (Just stack) in
    a == nt && isJust newStack && and (zipWith3 produces daughters (b ++ c:d) (stackLister b d (fromJust newStack)))
produces (LIT (Leaf a b _) daughters) nt stack = a == nt && null stack && null daughters
    -- ignore b (list of terminals) since it doesn't affect whether derivation is valid
-- produces _ _ _ = False
    -- adding a catchall (for now)... unsure if needed

-- mytree1 :: LITree
-- mytree1 = Bin ligr4 (Lef ligr7) (Bin ligr1 (Lef ligr8) (Lef ligr7))

tree1 :: LITree
tree1 = LIT ligr2 [LIT ligr4 [LIT ligr6 []]]

tree2 :: LITree
tree2 = LIT ligr1 [
            LIT ligr7 [],
            LIT ligr2 [
                LIT ligr3 [
                    LIT ligr8 [],
                    LIT ligr4 [
                        LIT ligr5 [
                            LIT ligr6 [],
                            LIT ligr9 []
                        ]
                    ],
                    LIT ligr10 []
                ]
            ]
        ]

tree3 :: LITree
tree3 = LIT ligr1 [
            LIT ligr7 [],
            LIT ligr2 [
                LIT ligr4 [
                    LIT ligr5 [
                        LIT ligr6 [],
                        LIT ligr9 []
                    ]
                ]
            ]
        ]

tree4 :: LITree
tree4 = LIT ligr2 [
            LIT ligr3 [
                LIT ligr8 [],
                LIT ligr4 [
                    LIT ligr6 []
                ],
                LIT ligr10 []
            ]
        ]

isSentence :: LITree -> Bool
isSentence tree = produces tree S []

yield :: LITree -> String
yield (LIT (Leaf a b _) d) = concat b
yield (LIT (Branch a b c d e _) daughters) = concat (map yield daughters)

-- LIG for displaying
newtype LIGRN = R Integer deriving (Show, Eq)

data LITN = LITN LIGRN [LITN] deriving (Show, Eq)

treen4 :: LITN
treen4 = LITN (R 2) [
            LITN (R 3) [
                LITN (R 8) [],
                LITN (R 4) [
                    LITN (R 6) []
                ],
                LITN (R 10) []
            ]
        ]

-- HG SECTION

-- data HGN = Single VN | Triple VN VN (Maybe VI) deriving (Show, Eq)

-- -- data HGRule = Wrap HGN (HGN, HGN) | Concat HGN [HGN] | Terminal HGN (VT,VT) deriving (Show, Eq)


-- convertLH :: LITN -> HGTree
-- convertLH lit = undefined

data RoseTree a = Bud a | RT a [RoseTree a] (RoseTree a) [RoseTree a] deriving (Show, Eq)

roseToTree :: (Show a) => RoseTree a -> Tree String
roseToTree (Bud b) = Node (show b) []
roseToTree (RT m l d r) = Node (show m) ((map roseToTree l) ++ (roseToTree d):(map roseToTree r))

printRose :: Show a => RoseTree a -> IO ()
printRose t = putStrLn $ drawTree $ roseToTree t

data PTree a = PT a (TContext a) deriving (Show, Eq)
data TContext a = EmptyContext | TC a [PTree a] (TContext a) [PTree a] deriving (Show, Eq)

-- next three functions are old; to be replaced by petrify2
getbud :: RoseTree a -> a
getbud (Bud b) = b
getbud (RT m l d r) = getbud d

petrify :: RoseTree a -> PTree a
petrify (Bud b) = PT b EmptyContext
petrify (RT m l d r) = PT (getbud d) (contextify (RT m l d r))

contextify :: RoseTree a -> TContext a
contextify (Bud b) = EmptyContext
contextify (RT m l d r) = TC m (map petrify l) (contextify d) (map petrify r)

-- can I do both getbud and contextify at the same time?
petrify2 :: RoseTree a -> PTree a
petrify2 (Bud b) = PT b EmptyContext
petrify2 (RT m l d r) = let PT b c = petrify2 d in PT b (TC m (map petrify2 l) c (map petrify2 r))

rtree1 :: RoseTree Int
rtree1 = RT 1 
            [Bud 7]
            (RT 2
                []
                (RT 3
                    [Bud 8]
                    (RT 4
                        []
                        (RT 5
                            []
                            (Bud 6)
                            [Bud 9]
                        )
                        []
                    )
                    [Bud 10]
                )
                []
            )
            []

rosify :: PTree a -> RoseTree a
rosify (PT b EmptyContext) = Bud b
rosify (PT b (TC m l d r)) = RT m (map rosify l) (rosify (PT b d)) (map rosify r)


-- HG section

-- data HGRule a = W1 | W2 | E | L a deriving (Show, Eq)
-- data HGTree a = HGT (HGRule a) [HGTree a] deriving (Show, Eq)

-- hgify :: PTree a -> HGTree a
-- hgify (PT b c) = HGT W2 [contexthg c, HGT (L b) []]

-- contexthg :: TContext a -> HGTree a
-- contexthg EmptyContext = HGT E []
-- contexthg (TC m l d r) = HGT (L m) ((map hgify l) ++ (contexthg d):(map hgify r))

-- data HGRule = W1 | W2 | E | L Int deriving (Show, Eq)
data HGRule = W1 VN VN VN VI | W2 VN VN | E VN | L Int VN | Lx Int deriving (Show, Eq)
data HGTree = HGT HGRule [HGTree] deriving (Show, Eq)

hgToTree :: HGTree -> Tree String
hgToTree (HGT r l) = Node (show r) (map hgToTree l)

printHG :: HGTree -> IO ()
printHG t = putStrLn $ drawTree $ hgToTree t

hgify :: PTree (Int, SC) -> HGTree
hgify (PT (b, s) EmptyContext) = HGT (Lx b) []
    -- if W2 is followed by empty context, it is trivial; you can remove the W2 and E
hgify (PT (b, s) c) = let x = (mother (getrule (conthead c))) in 
                      let y = (mother (getrule b)) in
                    HGT (W2 x y) [contexthg c y, HGT (Lx b) []]
    -- distinction between L rules and Lx rules is structural; all buds are Lx.
    -- do I ever need to reference what kind of rule each number is? eg Branch vs Leaf LIGrule?
    -- I don't think so, assuming that the LIG tree was well formed, ie. leaves only at leaves

emptycont :: TContext a -> Bool
emptycont EmptyContext = True
emptycont _ = False

conthead :: TContext (Int, SC) -> Int
conthead EmptyContext = 0
conthead (TC (m,_) _ _ _) = m

contexthg :: TContext (Int, SC) -> VN -> HGTree
contexthg EmptyContext y = HGT (E y) []
    -- write a case (similar to hgify above) where if W1 is followed by empty context, it is trivial and remove it
contexthg (TC (m, Push i) l d r) y = let (t,b) = splitcon i [] d in if emptycont t then HGT (L m y) ((map hgify l) ++ (contexthg b y):(map hgify r))
    else let x = (mother (getrule m)) in let z = (mother (getrule (conthead b))) in
        HGT (L m y) ((map hgify l) ++ (HGT (W1 x y z i) [contexthg t z, contexthg b y]):(map hgify r))
contexthg (TC (m, s) l d r) y = HGT (L m y) ((map hgify l) ++ (contexthg d y):(map hgify r))

splitcon :: VI -> [VI] -> TContext (a, SC) -> (TContext (a, SC), TContext (a, SC))
splitcon i is EmptyContext = (EmptyContext, EmptyContext)
splitcon i is (TC (m, s) l d r) = if null is && s == Pop i then (EmptyContext, (TC (m, s) l d r)) else
                                    let (t, b) = splitcon i (fromJust (changeStack s (Just is))) d in 
                                        ((TC (m, s) l t r), b)

splitcon2 (TC (m, Push i) l d r) = undefined
splitcon2 (TC (m, Pop i) l d r) = undefined

-- a test case on lists first
splitter :: Int -> [Int] -> ([Int], [Int])
splitter i [] = ([],[])
splitter i (x:xs) = if x == i then ([], x:xs) else
                    let (a, b) = splitter i xs in (x:a, b)

ratree1 :: RoseTree (Int, SC)
ratree1 = RT (1, Push 1) 
            [Bud (7, NoChange)]
            (RT (2, NoChange)
                []
                (RT (3, NoChange)
                    [Bud (8, NoChange)]
                    (RT (4, NoChange)
                        []
                        (RT (5, Pop 1)
                            []
                            (Bud (6, NoChange))
                            [Bud (9, NoChange)]
                        )
                        []
                    )
                    [Bud (10, NoChange)]
                )
                []
            )
            []

hgtree1 = hgify $ petrify2 ratree1