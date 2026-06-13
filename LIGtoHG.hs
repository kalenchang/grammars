{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use const" #-}
{-# HLINT ignore "Use concatMap" #-}
{-# HLINT ignore "Redundant bracket" #-}
module LIGtoHG where

import Prelude
import Data.Maybe ( isJust, fromJust )
import Data.Tree

import Printing
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
parseRose (LIT r@(Leaf a b) t) = Bud r
parseRose (LIT r@(Branch a b c d _) t) = let (ls,c:rs) = splitat (length b) t in RT r (map parseRose ls) (parseRose c) (map parseRose rs)

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

-- Bool indicates whether the NT before it is a barred symbol or not
data HGTransNT nts ind = Sng nts Bool | Sngi nts Bool ind | Trp nts nts Bool | Trpi nts nts Bool ind deriving Eq

-- regular show instance for triple categories
-- instance (Show nts, Show ind) => Show (HGTransNT nts ind) where
--     show (Sng a bar) = show a ++ if bar then "'" else ""
--     show (Trp a b bar e) = '(':(show a) ++ ',':(show b) ++ (if bar then "'" else "") ++ ',':(case e of {Just i -> show i; Nothing -> "0"}) ++ ")"

-- show instance for triple categories for latex
instance (Show nts, Show ind) => Show (HGTransNT nts ind) where
    show (Sng a bar) = show a
    show (Sngi a bar c) = show a ++ show c
    show (Trp a b bar) = "" ++ (show a) ++ "/" ++ (show b) ++ ""
    show (Trpi a b bar e) = "" ++ (show a) ++ "/" ++ (show b) ++ "/" ++ show e ++ ""

instance (Texable nts, Texable ind) => Texable (HGTransNT nts ind) where
    texify (Sng a bar) = texify a
    texify (Sngi a bar c) = texify a ++ "\\rais{" ++ texify c ++ "}"
    texify (Trp a b bar) = "\\tripcat{" ++ (texify a) ++ "}{" ++ (\x -> if bar then "\\xbar{" ++ x ++ "}" else x) (texify b) ++ "}{}"
    texify (Trpi a b bar e) = "\\tripcat{" ++ (texify a) ++ "}{" ++ (\x -> if bar then "\\xbar{" ++ x ++ "}" else x) (texify b) ++ "}{" ++ texify e ++ "}"

-- data HGRule nts ts = W1 nts nts nts VI | W2 nts nts | E nts | L (LIGRule nts ts) nts | Lx (LIGRule nts ts) deriving Eq

-- constructors for HGRules that come from an LIG
makeW1rule :: nts -> nts -> nts -> ind -> HGRule (HGTransNT nts ind) ts
makeW1rule a d b e = Wrap (Trpi a d False e) (Trp a b True) (Trpi b d True e)

makeW2rule :: nts -> nts -> HGRule (HGTransNT nts ind) ts
makeW2rule a b = Wrap (Sng a False) (Trp a b True) (Sng b True)

makeErule :: nts -> HGRule (HGTransNT nts ind) ts
makeErule a = Leafh (Trp a a False) [] []

makeLrule :: (LIGRule nts ts ind) -> nts -> Bool -> HGRule (HGTransNT nts ind) ts
-- makeLrule (Branch a b c d e) g bar = let (k, l) = case e of {NoChange -> (Nothing, Nothing); 
--                                                             Push i -> (Nothing, Just i);
--                                                             Pop i -> (Just i, Nothing)} in
--                 Concat (Trp a g bar k) (map (\x -> Sng x False) b) (Trp c g False l) (map (\x -> Sng x False) d)
makeLrule (Branch a b c d NoChange) g bar = Concat (Trp a g bar) (map (\x -> Sng x False) b) (Trp c g False) (map (\x -> Sng x False) d)
makeLrule (Branch a b c d (Push i)) g bar = Concat (Trp a g bar) (map (\x -> Sng x False) b) (Trpi c g False i) (map (\x -> Sng x False) d)
makeLrule (Branch a b c d (Pop i)) g bar = Concat (Trpi a g bar i) (map (\x -> Sng x False) b) (Trp c g False) (map (\x -> Sng x False) d)
makeLxrule :: (LIGRule nts ts ind) -> Bool -> HGRule (HGTransNT nts ind) ts
makeLxrule (Leaf a b) bar = Leafh (Sng a bar) [] b

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
hgify (PT r EmptyContext) = HGT (makeLxrule r False) []
    -- if W2 is followed by empty context, it is trivial; you can remove the W2 and E
hgify (PT r cont) = let x = (mother $ conthead cont) in 
                      let y = (mother r) in
                    HGT (makeW2rule x y) [contexthg cont y True, HGT (makeLxrule r True) []]
    -- distinction between L rules and Lx rules is structural; all buds are Lx.
    -- do I ever need to reference what kind of rule each number is? eg Branch vs Leaf LIGrule?
    -- I don't think so, assuming that the LIG tree was well formed, ie. leaves only at leaves

emptycont :: TContext a -> Bool
emptycont EmptyContext = True
emptycont _ = False

conthead :: TContext (LIGRule nts ts ind) -> LIGRule nts ts ind
conthead EmptyContext = undefined
conthead (TC m _ _ _) = m

contexthg :: (Eq ind) => TContext (LIGRule nts ts ind) -> nts -> Bool -> HGTree (HGTransNT nts ind) ts
contexthg EmptyContext y bar = if not bar then HGT (makeErule y) [] else undefined
    -- write a case (similar to hgify above) where if W1 is followed by empty context, it is trivial and remove it
contexthg (TC m@(Branch _ _ _ _ (Push i)) l d r) y bar = let (t,b) = splitcon i [] d in 
    if emptycont t then 
        HGT (makeLrule m y bar) ((map hgify l) ++ (contexthg b y False):(map hgify r))
    else 
        let x = mother $ conthead t 
            z = mother $ conthead b
        in HGT (makeLrule m y bar) ((map hgify l) ++ (HGT (makeW1rule x y z i) [contexthg t z True, contexthg b y True]):(map hgify r))
contexthg (TC m l d r) y bar = HGT (makeLrule m y bar) ((map hgify l) ++ (contexthg d y False):(map hgify r))

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

g1r1 = Branch S [A] S [] (Push 1)
g1r2 = Branch S [C] S [] (Push 3)
g1r3 = Branch S [] T [] (NoChange)
g1r4 = Branch T [B] T [B] (NoChange)
g1r5 = Branch T [D] T [D] (NoChange)
g1r6 = Branch T [] U [] (NoChange)
g1r7 = Branch U [A] U [] (Pop 1)
g1r8 = Branch U [C] U [] (Pop 3)
g1r9 = Leaf U []
g1r10 = Leaf A ["a"]
g1r11 = Leaf B ["b"]
g1r12 = Leaf C ["c"]
g1r13 = Leaf D ["d"]

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

g2r1 = Branch S [] S [B] (Push 2)
g2r2 = Branch S [] S [D] (Push 4)
g2r3 = Branch S [] T [] (NoChange)
g2r4 = Branch T [A] T [A] (NoChange)
g2r5 = Branch T [C] T [C] (NoChange)
g2r6 = Branch T [] U [] (NoChange)
g2r7 = Branch U [] U [B] (Pop 2)
g2r8 = Branch U [] U [D] (Pop 4)
g2r9 = Leaf U []
g2r10 = Leaf A ["a"]
g2r11 = Leaf B ["b"]
g2r12 = Leaf C ["c"]
g2r13 = Leaf D ["d"]

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


----------------------
-- grammar 3: w w

g3r1 = Branch S [A] S [] (Push 1)
g3r2 = Branch S [B] S [] (Push 2)
g3r3 = Branch S [] T [] (NoChange)
g3r4 = Branch T [] T [A] (Pop 1)
g3r5 = Branch T [] T [B] (Pop 2)
g3r6 = Leaf T []
g3r7 = Leaf A ["a"]
g3r8 = Leaf B ["b"]

-- abb abb
g3t1 =  LIT g3r1 [
            LIT g3r7 [],
            LIT g3r2 [
                LIT g3r8 [],
                LIT g3r2 [
                    LIT g3r8 [],
                    LIT g3r3 [
                        LIT g3r5 [
                            LIT g3r5 [
                                LIT g3r4 [
                                    LIT g3r6 [],
                                    LIT g3r7 []
                                ],
                                LIT g3r8 []
                            ],
                            LIT g3r8 []
                        ]
                    ]
                ]
            ]
        ]


---------------------
-- grammar 4: ai bj ci dj

g4r1 = Branch S [A] S [] (Push 1)
g4r2 = Branch S [] T [] (NoChange)
g4r3 = Branch T [B] T [D] (NoChange)
g4r4 = Branch T [] U [] (NoChange)
g4r5 = Branch U [C] U [] (Pop 1)
g4r6 = Leaf U []
g4r7 = Leaf A ["a"]
g4r8 = Leaf B ["b"]
g4r9 = Leaf C ["c"]
g4r10 = Leaf D ["d"]

-- aa b cc d
g4t1 = LIT g4r1 [
            LIT g4r7 [],
            LIT g4r1 [
                LIT g4r7 [],
                LIT g4r2 [
                    LIT g4r3 [
                        LIT g4r8 [],
                        LIT g4r4 [
                            LIT g4r5 [
                                LIT g4r9 [],
                                LIT g4r5 [
                                    LIT g4r9 [],
                                    LIT g4r6 []
                                ]
                            ]
                        ],
                        LIT g4r10 []
                    ]
                ]
            ]
        ]


---------------------------------------
-- NEW translation: LHT (top down!!) --
---------------------------------------

hgsided (cat,[]) = NTO (Sng cat False)
hgsided (cat,[index]) = NTO (Sngi cat False index)

makeBranchhx (Branchx a i b (c,ci) d) sts = HGXR (Trpi a (last (c:sts)) False i) (ConcatO (map hgsided b) (WrapO $ zipWith3 (\x y z -> NTO (Trpi x y False z)) (c:sts) sts ci) (map hgsided d))       
makeNopushhx (Branchx a i b (c,[]) d) = HGXR (Trpi a c False i) (ConcatO (map hgsided b) (LeafO [] []) (map hgsided d))
makeLeafhx (Leafx a b) = HGXR (Sng a False) (LeafO [] b)
makeFillhx a b i = HGXR (Sngi a False i) (WrapO [NTO (Trpi a b False i), NTO (Sng b False)])
makeEmptyhx a = HGXR (Trp a a False) (LeafO [] [])

parseRosex (Node r@(Leafx _ _) []) = Bud r
parseRosex (Node r@(Branchx _ _ b c d) ts) = let (ls, cd:rs) = splitAt (length b) ts in RT r (map parseRosex ls) (parseRosex cd) (map parseRosex rs)

data PTreeX a = PTX a (TContextX a) deriving (Show, Eq)
data TContextX a = EmptyX | TCX a [Tree a] (TContextX a) [Tree a] deriving (Show, Eq)

-- petrifyx :: RoseTree a -> PTreeX a
-- petrifyx (Bud b) = PTX b EmptyX
-- petrifyx (RT m l d r) = let PTX b c = petrifyx d in PTX b (TCX m l c r)

petrose (Node r@(Leafx _ _) []) = PTX r EmptyX
petrose (Node r@(Passx _ b _ _) ts) = let (ls, cd:rs) = splitAt (length b) ts in
                let PTX bud cont = petrose cd in
                    PTX bud (TCX r ls cont rs)
petrose (Node r@(Branchx _ _ b c d) ts) = let (ls, cd:rs) = splitAt (length b) ts in
                let PTX bud cont = petrose cd in
                    PTX bud (TCX r ls cont rs)

-- lht :: (Eq nts, Eq ind) => (Tree (LIGXRule nts ts ind)) -> Tree (HGXRule (HGTransNT nts ind) ts)
lht (Node r@(Leafx a b) []) = Node (makeLeafhx r) []
lht t@(Node r@(Branchx a i _ _ _) _) = let (PTX lx@(Leafx x _) cont) = petrose t in
                    let [headt] = (lht' cont x) in
                        Node (makeFillhx a x i) [headt, Node (makeLeafhx lx) []]

-- lht' :: (Eq nts, Eq ind) => (Tree (LIGXRule nts ts ind)) -> [Tree (HGXRule (HGTransNT nts ind) ts)]
lht' EmptyX x = []
lht' (TCX m@(Branchx a i b (c,[]) d) l dc r) x = (Node (makeNopushhx m) (map lht l ++ map lht r)):(lht' dc x)
lht' (TCX m@(Branchx a i b (c,ci) d) l dc r) x = let (treelist, rank) = (lht' dc x, length ci) in
    let (lf, lb) = (take rank treelist, drop rank treelist) in 
    (Node (makeBranchhx m (map rtdn lf)) (map lht l ++ lf ++ map lht r)):lb
        where rtdn (Node (HGXR (Trpi _ denom _ _) _) _) = denom


-- > latexTree $ threeLatex gx1t1
-- > latexTree $ hgxtoThreeLatex $ lht gx1t1

