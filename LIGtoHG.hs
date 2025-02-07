{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use const" #-}
{-# HLINT ignore "Use concatMap" #-}
{-# HLINT ignore "Redundant bracket" #-}
module LIGtoHG where

import Prelude
import Data.Maybe ( isJust, fromJust )
import Data.Tree
import TreePrint
import LIG
import HG


-----------------------------------------
-- Rosetree section

-- data HGN = Single VN | Triple VN VN (Maybe VI) deriving (Show, Eq)

-- -- data HGRule = Wrap HGN (HGN, HGN) | Concat HGN [HGN] | Terminal HGN (VT,VT) deriving (Show, Eq)


-- convertLH :: LITN -> HGTree
-- convertLH lit = undefined

-- seems to be the same as splitAt in Prelude but only traverses the list once?
splitat :: Int -> [a] -> ([a],[a])
splitat _ [] = ([],[])
splitat i (x:xs) = if i == 0 then ([],x:xs) else let (y,z) = splitat (i-1) xs in (x:y,z)

data RoseTree a = Bud a | RT a [RoseTree a] (RoseTree a) [RoseTree a] deriving (Show, Eq)

roseToTree :: (Show a) => RoseTree a -> Tree String
roseToTree (Bud b) = Node (show b) []
roseToTree (RT m l d r) = Node (show m) ((map roseToTree l) ++ (roseToTree d):(map roseToTree r))

printRose :: Show a => RoseTree a -> IO ()
printRose t = putStrLn $ drawTree $ roseToTree t

-- convert LITrees into RoseTrees, i.e. [lefts] center [rights]
-- ideally Leaf rules would be at and only at leaf nodes, but currently no way to guarantee that...
-- anyone can give a maliciously bad derivation...
parseRose :: LITree nts ts ind -> RoseTree (LIGRule nts ts ind)
parseRose (LIT r []) = Bud r
parseRose (LIT r@(Leaf a b _) t) = Bud r
parseRose (LIT r@(Branch a b c d _ _) t) = let (ls,c:rs) = splitat (length b) t in RT r (map parseRose ls) (parseRose c) (map parseRose rs)

data PTree a = PT a (TContext a) deriving (Show, Eq)
data TContext a = EmptyContext | TC a [PTree a] (TContext a) [PTree a] deriving (Show, Eq)

-- next three functions are old; to be replaced by petrify2
-- getbud :: RoseTree a -> a
-- getbud (Bud b) = b
-- getbud (RT m l d r) = getbud d

-- petrify :: RoseTree a -> PTree a
-- petrify (Bud b) = PT b EmptyContext
-- petrify (RT m l d r) = PT (getbud d) (contextify (RT m l d r))

-- contextify :: RoseTree a -> TContext a
-- contextify (Bud b) = EmptyContext
-- contextify (RT m l d r) = TC m (map petrify l) (contextify d) (map petrify r)

-- can I do both getbud and contextify at the same time? yes, see here:
petrify :: RoseTree a -> PTree a
petrify (Bud b) = PT b EmptyContext
petrify (RT m l d r) = let PT b c = petrify d in PT b (TC m (map petrify l) c (map petrify r))

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

-----------------------------------------
-- HG section

-- data HGRule a = W1 | W2 | E | L a deriving (Show, Eq)
-- data HGTree a = HGT (HGRule a) [HGTree a] deriving (Show, Eq)

-- hgify :: PTree a -> HGTree a
-- hgify (PT b c) = HGT W2 [contexthg c, HGT (L b) []]

-- contexthg :: TContext a -> HGTree a
-- contexthg EmptyContext = HGT E []
-- contexthg (TC m l d r) = HGT (L m) ((map hgify l) ++ (contexthg d):(map hgify r))

data HGTransNT nts ind = Sng nts | Trp nts nts (Maybe ind) deriving Eq

instance (Show nts, Show ind) => Show (HGTransNT nts ind) where
    show (Sng a) = show a
    show (Trp a b e) = '(':(show a) ++ ',':(show b) ++ ',':(case e of {Just i -> show i; Nothing -> "0"}) ++ ")"

-- data HGRule nts ts = W1 nts nts nts VI | W2 nts nts | E nts | L (LIGRule nts ts) nts | Lx (LIGRule nts ts) deriving Eq

-- constructors for HGRules that come from an LIG
makeW1rule :: nts -> nts -> nts -> ind -> HGRule (HGTransNT nts ind) ts
makeW1rule a b d e = Wrap (Trp a d (Just e)) (Trp a b Nothing) (Trp b d (Just e)) 1 -- labels will all be 1 for now...

makeW2rule :: nts -> nts -> HGRule (HGTransNT nts ind) ts
makeW2rule a b = Wrap (Sng a) (Trp a b Nothing) (Sng b) 2

makeErule :: nts -> HGRule (HGTransNT nts ind) ts
makeErule a = Leafh (Trp a a Nothing) [] [] 3

makeLrule :: (LIGRule nts ts ind) -> nts -> HGRule (HGTransNT nts ind) ts
makeLrule (Branch a b c d e f) g = let (k, l) = case e of {NoChange -> (Nothing, Nothing); 
                                                            Push i -> (Nothing, Just i);
                                                            Pop i -> (Just i, Nothing)} in
                Concat (Trp a g k) (map Sng b) (Trp c g l) (map Sng d) f

makeLxrule :: (LIGRule nts ts ind) -> HGRule (HGTransNT nts ind) ts
makeLxrule (Leaf a b c) = Leafh (Sng a) [] b c

-- old show code; the show function should fall out from the rule constructors + showing those
{-
instance (Show nts, Show ts) => Show (HGRule nts ts) where
    show (W1 a b d e) = '(':(show a) ++ ',':(show d) ++ ',':(show e) ++ ") -W-> (" ++ (show a)++ ',':(show b) ++ ",0) (" ++ (show b) ++ ',':(show d) ++ ',':(show e) ++ ")"
    show (W2 a b) = (show a) ++ " -W-> (" ++ (show a) ++ ',':(show b) ++ ",0) " ++ (show b)
    show (E a) = '(':(show a) ++ ',':(show a) ++ ",0) --> 0 , 0"
    show (L r@(Branch a b c d e f) g) = let j = (show $ (length b)+1) in
                                let (k, l) = case e of {NoChange -> ("0) -C" ++ j ++ "->","0)"); 
                                                          Push i -> ("0) -C" ++ j ++ "->",(show i) ++ ")");
                                                          Pop i -> ((show i) ++ ") -C" ++ j ++ "->","0)")} in
            '(':(show a) ++ ',':(show g) ++ ',':k ++ (insertSpaces b) ++ " (" ++ (show c) ++ ',':(show g) ++ ',':l ++ (insertSpaces d)
    show (Lx r@(Leaf a b c)) = (show a) ++ " --> 0 , " ++ show b
-}


-- TODO: define category, yield of a tree, then define functions to convert
-- maybe just define a fold function (HGTree -> String) -> HGTree -> Tree String

printHG :: (Show nts, Show ts) => HGTree nts ts -> IO ()
printHG t = putStrLn $ drawTree $ hgtoRuleTree t

hgify :: Eq ind => PTree (LIGRule nts ts ind) -> HGTree (HGTransNT nts ind) ts
hgify (PT r EmptyContext) = HGT (makeLxrule r) []
    -- if W2 is followed by empty context, it is trivial; you can remove the W2 and E
hgify (PT r cont) = let x = (mother $ conthead cont) in 
                      let y = (mother r) in
                    HGT (makeW2rule x y) [contexthg cont y, HGT (makeLxrule r) []]
    -- distinction between L rules and Lx rules is structural; all buds are Lx.
    -- do I ever need to reference what kind of rule each number is? eg Branch vs Leaf LIGrule?
    -- I don't think so, assuming that the LIG tree was well formed, ie. leaves only at leaves

emptycont :: TContext a -> Bool
emptycont EmptyContext = True
emptycont _ = False

conthead :: TContext (LIGRule nts ts ind) -> LIGRule nts ts ind
conthead EmptyContext = undefined
conthead (TC m _ _ _) = m

contexthg :: (Eq ind) => TContext (LIGRule nts ts ind) -> nts -> HGTree (HGTransNT nts ind) ts
contexthg EmptyContext y = HGT (makeErule y) []
    -- write a case (similar to hgify above) where if W1 is followed by empty context, it is trivial and remove it
contexthg (TC m@(Branch _ _ _ _ (Push i) _) l d r) y = let (t,b) = splitcon i [] d in 
    if emptycont t then 
        HGT (makeLrule m y) ((map hgify l) ++ (contexthg b y):(map hgify r))
    else 
        let x = mother $ conthead t 
            z = mother $ conthead b
        in HGT (makeLrule m y) ((map hgify l) ++ (HGT (makeW1rule x y z i) [contexthg t z, contexthg b y]):(map hgify r))
contexthg (TC m l d r) y = HGT (makeLrule m y) ((map hgify l) ++ (contexthg d y):(map hgify r))

splitcon :: Eq ind => ind -> [ind] -> TContext (LIGRule nts ts ind) -> (TContext (LIGRule nts ts ind), TContext (LIGRule nts ts ind))
splitcon i is EmptyContext = (EmptyContext, EmptyContext)
splitcon i is (TC m l d r) = let s = change m in
                                if null is && s == Pop i then (EmptyContext, (TC m l d r)) else
                                    let (t, b) = splitcon i (fromJust (changeStack s (Just is))) d in 
                                        ((TC m l t r), b)

-- splitcon2 (TC (m, Push i) l d r) = undefined
-- splitcon2 (TC (m, Pop i) l d r) = undefined

-- a test case on lists first
splitter :: Int -> [Int] -> ([Int], [Int])
splitter i [] = ([],[])
splitter i (x:xs) = if x == i then ([], x:xs) else
                    let (a, b) = splitter i xs in (x:a, b)

ratree1 :: RoseTree (Int, SC VI)
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

ligtohg :: Eq ind => LITree nts ts ind -> HGTree (HGTransNT nts ind) ts
ligtohg = hgify . petrify . parseRose

-- eg, try:
-- > latexTree $ hgToTree $ ligtohg tree2
-- > printTree $ hgToTree $ ligtohg tree2

-- strong equivalence translation
-- start with an algebraic function which evaluates a derivation tree

countnodes :: LITree nts ts ind -> Int
countnodes (LIT m d) = 1 + sum (map countnodes d)

measureHG :: LITree nts ts ind -> (LITree nts ts ind -> a) -> a
measureHG = undefined


-------------------------------
-- grammar 1: w v wR vR

g1r1 = Branch S [A] S [] (Push 1) 101
g1r2 = Branch S [C] S [] (Push 3) 102
g1r3 = Branch S [] T [] (NoChange) 103
g1r4 = Branch T [B] T [B] (NoChange) 104
g1r5 = Branch T [D] T [D] (NoChange) 105
g1r6 = Branch T [] U [] (NoChange) 106
g1r7 = Branch U [A] U [] (Pop 1) 107
g1r8 = Branch U [C] U [] (Pop 3) 108
g1r9 = Leaf U [] 109
g1r10 = Leaf A ["a"] 110
g1r11 = Leaf B ["b"] 111
g1r12 = Leaf C ["c"] 112
g1r13 = Leaf D ["d"] 113

-- acc bdb cca bdb
g1t1 =  LIT g1r1 [
            LIT g1r10 [],
            LIT g1r2 [
                LIT g1r12 [],
                LIT g1r2 [
                    LIT g1r12 [],
                    LIT g1r3 [
                        LIT g1r4 [
                            LIT g1r11 [],
                            LIT g1r5 [
                                LIT g1r13 [],
                                LIT g1r4 [
                                    LIT g1r11 [],
                                    LIT g1r6 [
                                        LIT g1r8 [
                                            LIT g1r12 [],
                                            LIT g1r8 [
                                                LIT g1r12 [],
                                                LIT g1r7 [
                                                    LIT g1r10 [],
                                                    LIT g1r9 []
                                                ]
                                            ]
                                        ]
                                    ],
                                    LIT g1r11 []
                                ],
                                LIT g1r13 []
                            ],
                            LIT g1r11 []
                        ]
                    ]
                ]
            ]
        ]

g1t2 =  LIT g1r1 [
            LIT g1r10 [],
            LIT g1r2 [
                LIT g1r12 [],
                LIT g1r2 [
                    LIT g1r12 [],
                    LIT g1r3 [
                        LIT g1r4 [
                            LIT g1r11 [],
                            LIT g1r4 [
                                LIT g1r11 [],
                                LIT g1r5 [
                                    LIT g1r13 [],
                                    LIT g1r5 [
                                        LIT g1r13 [],
                                        LIT g1r6 [
                                            LIT g1r8 [
                                                LIT g1r12 [],
                                                LIT g1r8 [
                                                    LIT g1r12 [],
                                                    LIT g1r7 [
                                                        LIT g1r10 [],
                                                        LIT g1r9 []
                                                    ]
                                                ]
                                            ]
                                        ],
                                        LIT g1r13 []
                                    ],
                                    LIT g1r13 []
                                ],
                                LIT g1r11 []
                            ],
                            LIT g1r11 []
                        ]
                    ]
                ]
            ]
        ]

-- > printTree $ ligtoRuleTree g1t1
-- > latexTree $ ligtoRuleTree g1t1
-- > latexTree $ ligtoCatTree g1t1
-- > latexTree $ hgtoAllTree $ ligtohg g1t1


--------------------------------
-- grammar 2: w v wR vR, but (only?) the other way LIG can do it

g2r1 = Branch S [] S [B] (Push 2) 201
g2r2 = Branch S [] S [D] (Push 4) 202
g2r3 = Branch S [] T [] (NoChange) 203
g2r4 = Branch T [A] T [A] (NoChange) 204
g2r5 = Branch T [C] T [C] (NoChange) 205
g2r6 = Branch T [] U [] (NoChange) 206
g2r7 = Branch U [] U [B] (Pop 2) 207
g2r8 = Branch U [] U [D] (Pop 4) 208
g2r9 = Leaf U [] 209
g2r10 = Leaf A ["a"] 210
g2r11 = Leaf B ["b"] 211
g2r12 = Leaf C ["c"] 212
g2r13 = Leaf D ["d"] 213

g2t1 =  LIT g2r1 [
            LIT g2r2 [
                LIT g2r1 [
                    LIT g2r3 [
                        LIT g2r4 [
                            LIT g2r10 [],
                            LIT g2r5 [
                                LIT g2r12 [],
                                LIT g2r5 [
                                    LIT g2r12 [],
                                    LIT g2r6 [
                                        LIT g2r7 [
                                            LIT g2r8 [
                                                LIT g2r7 [
                                                    LIT g2r9 [],
                                                    LIT g2r11 []
                                                ],
                                                LIT g2r13 []
                                            ],
                                            LIT g2r11 []
                                        ]
                                    ],
                                    LIT g2r12 []
                                ],
                                LIT g2r12 []
                            ],
                            LIT g2r10 []
                        ]
                    ],
                    LIT g2r11 []
                ],
                LIT g2r13 []
            ],
            LIT g2r11 []
        ]
