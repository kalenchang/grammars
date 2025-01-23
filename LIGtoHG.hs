{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use const" #-}
{-# HLINT ignore "Use concatMap" #-}
{-# HLINT ignore "Redundant bracket" #-}
module LIGtoHG where

import Prelude
import Data.Maybe ( isJust, fromJust )
import Data.Tree
import TreePrint

-- nonterminals; Vt = transitive verb, Ve = embedding verb, Tr = trace
data VN = S | T | U | A | B | C | D deriving (Show, Eq)

-- terminals
type VT = String

-- indices
type VI = Int

-- stack change
data SC = NoChange | Push VI | Pop VI deriving (Show, Eq)

-- two kinds of LIG rules: Branch node or a Leaf node
-- Branch: 1 rewrites as 2 3 4, where 3 is the distinguished daughter, with stack change 5
-- Leaf: 1 rewrites as 2
-- data LIGRule = Branch VN [VN] VN [VN] SC Int | Leaf VN [VT] Int deriving (Show, Eq)

data LIGRule = Branch {mother :: VN, lefts :: [VN], daughter :: VN, rights :: [VN], change :: SC, label :: Int} 
        | Leaf {mother :: VN, terms :: VT, label :: Int} deriving Eq

-- i'm starting to feel like branch rules and leaf rules should be their own kinds of rules... but idk
-- data LIGRule = Branch LIGBranchRule | Leaf LIGLeafRule deriving (Show, Eq)

-- data LIGBranchRule = LIGBranchRule {mother :: VN, lefts :: [VN], daughter :: VN, rights :: [VN], change :: SC, label :: Int} deriving (Show, Eq)
-- data LIGLeafRule = LIGLeafRule {mother :: VN, terms :: [VT], label :: Int} deriving (Show, Eq)

-- insertSpaces :: Show a => [a] -> String
-- insertSpaces [] = ""
-- insertSpaces (x:xs) = ' ':(show x ++ insertSpaces xs)

-- insertSpaces' :: [String] -> String
-- insertSpaces' [] = ""
-- insertSpaces' (x:xs) = ' ':(x ++ insertSpaces' xs)

instance Show LIGRule where
    show (Branch a b c d e f) = let (s1, s2) = case e of {NoChange -> ("[..] ->","[..]"); 
                                                          Push i -> ("[..] ->","[" ++ (show i) ++ "..]");
                                                          Pop i -> ("[" ++ (show i) ++ "..] ->","[..]")} in
            (show a) ++ s1 ++ (insertSpaces b) ++ ' ':(show c) ++ s2 ++ (insertSpaces d)
    show (Leaf a b c) = (show a) ++ "[] -> " ++ b

newtype LIG = LIG ([VN], [VT], [VI], VN, [LIGRule])

-- list of rules
ligr1, ligr2, ligr3, ligr4, ligr5, ligr6, ligr7, ligr8, ligr9, ligr10, ligr0 :: LIGRule
ligr1 = Branch S [A] S [] (Push 1) 1
ligr2 = Branch S [] T [] NoChange 2 
ligr3 = Branch T [B] T [D] NoChange 3
ligr4 = Branch T [] U [] NoChange 4
ligr5 = Branch U [] U [C] (Pop 1) 5
ligr6 = Leaf U "" 6
ligr7 = Leaf A "a" 7
ligr8 = Leaf B "b" 8
ligr9 = Leaf C "c" 9
ligr10 = Leaf D "d" 10
-- dummy rule
ligr0 = Branch S [] T [] NoChange 0

ligrlist :: [LIGRule]
ligrlist = [ligr1, ligr2, ligr3, ligr4, ligr5, ligr6, ligr7, ligr8, ligr9, ligr10]

lookupLIGR :: Int -> [LIGRule] -> LIGRule
lookupLIGR n (x:xs) = if label x == n then x else lookupLIGR n xs
lookupLIGR _ [] = ligr0

getrule :: Int -> LIGRule
getrule x = lookupLIGR x ligrlist

data LITree = LIT LIGRule [LITree] deriving (Show, Eq)
-- is it possible/better to just use Tree LIGRule?

-- changeStack tries to do the stackchange on the given stack, returns Nothing if not possible
-- changeStack assumes you are working top down, so a Push i rule has the designate daughter's stack
--   one longer than the mother's
changeStack :: SC -> Maybe [VI] -> Maybe [VI]
changeStack _ Nothing = Nothing
changeStack NoChange s = s
changeStack (Push i) (Just s) = Just (i:s)
changeStack (Pop i) (Just []) = Nothing
changeStack (Pop i) (Just (x:s)) = if x == i then Just s else Nothing

-- stackUp does the same thing as changeStack, except working bottom up
stackUp :: SC -> Maybe [VI] -> Maybe [VI]
stackUp _ Nothing = Nothing
stackUp NoChange s = s
stackUp (Pop i) (Just s) = Just (i:s)
stackUp (Push i) (Just []) = Nothing
stackUp (Push i) (Just (x:s)) = if x == i then Just s else Nothing

-- given 3 arguments, l, r, s, where s is a list of b
-- returns a list of lists of b, where s is the len(l)+1th item of the list,
-- with len(l) and len(r) empty stacks to the left and right of s
-- use case: pass the stack to the designated daughter, and all other daughters get empty stacks
stackLister :: [a] -> [a] -> [b] -> [[b]]
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

extract :: Int -> [a] -> (a,[a])
extract _ [] = undefined
extract i (x:xs) = removeIndex i (x,xs)
    where
        -- removeIndex :: Int -> (a,[a]) -> (a,[a])
        removeIndex _ (x,[]) = (x,[])
        removeIndex i (x,y:ys) = if i == 0 then (x,y:ys) else let (z,zs) = (removeIndex (i-1) (y,ys)) in (z, x:zs)

-- another alternative to produces: category :: LITree -> Maybe (VN, [VI])
-- category of a tree is either a NT + stack, or it's nothing if the tree is invalid
category :: LITree -> Maybe (VN, [VI])
category (LIT (Leaf a _ _) daughters) = if null daughters then Just (a, []) else Nothing
category (LIT (Branch a b c d e _) daughters) = if correctDaughters && isJust newStack then Just (a, fromJust newStack) else Nothing
    where
        (desig,rest) = extract (length b) daughters
        correctDaughters = and (zipWith checksides rest (b ++ d)) && checkmiddle 
        -- dt = daughter, n = nonterminal, s = stack
        checksides = \dt -> \n -> case category dt of {Just (x1, x2) -> x1 == n && x2 == []; Nothing -> False}
        checkmiddle = case category desig of {Just (x1, x2) -> x1 == c; Nothing -> False}
        newStack = case category desig of {Just (x1, x2) -> stackUp e (Just x2); Nothing -> Nothing}

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

-- part of tree2 that should be S[1]
tree2' = LIT ligr2 [
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
yield (LIT (Leaf a b _) d) = b
yield (LIT (Branch a b c d e _) daughters) = concat (map yield daughters)

-- show an LIG tree using only its rule label
ligtoLabelTree :: LITree -> Tree String
ligtoLabelTree (LIT r t) = Node (show $ label r) (map ligtoLabelTree t)

-- show an LIG tree using the full rule
ligtoRuleTree :: LITree -> Tree String
ligtoRuleTree (LIT r t) = Node (show r) (map ligtoRuleTree t)

-- printTree :: Tree String -> IO ()
-- printTree t = putStrLn $ drawTree t

-- doesn't show stack; only shows the left side of each rule as the node
-- technically Leaf nodes should not have any daughters, so t in the Leaf line should be []
-- but also nothing in the data structure is stopping Leaf from having daughters
ligtoLeftsTree :: LITree -> Tree String
ligtoLeftsTree (LIT (Leaf a b _) t) = Node (show a ++ '\n':b) (map ligtoLeftsTree t)
ligtoLeftsTree (LIT r t) = Node (show $ mother r) (map ligtoLeftsTree t)

-- shows the category of the subtree as indicated by the `category' function
-- ought to implement some kind of memoization so it does not need to calculate the subtree's categories multiple times
ligtoCatTree :: LITree -> Tree String
ligtoCatTree (LIT r t) = Node (case category (LIT r t) of {Just (cat,stack) -> show cat ++ show stack; Nothing -> "n/a"}) (map ligtoCatTree t)

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
parseRose :: LITree -> RoseTree LIGRule
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

-- data HGRule = W1 | W2 | E | L Int deriving (Show, Eq)
data HGRule = W1 VN VN VN VI | W2 VN VN | E VN | L LIGRule VN | Lx LIGRule deriving Eq
instance Show HGRule where
    show (W1 a b d e) = '(':(show a) ++ ',':(show d) ++ ',':(show e) ++ ") -W-> (" ++ (show a)++ ',':(show b) ++ ",0) (" ++ (show b) ++ ',':(show d) ++ ',':(show e) ++ ")"
    show (W2 a b) = (show a) ++ " -W-> (" ++ (show a) ++ ',':(show b) ++ ",0) " ++ (show b)
    show (E a) = '(':(show a) ++ ',':(show a) ++ ",0) --> 0 , 0"
    show (L r@(Branch a b c d e f) g) = let j = (show $ (length b)+1) in
                                let (k, l) = case e of {NoChange -> ("0) -C" ++ j ++ "->","0)"); 
                                                          Push i -> ("0) -C" ++ j ++ "->",(show i) ++ ")");
                                                          Pop i -> ((show i) ++ ") -C" ++ j ++ "->","0)")} in
            '(':(show a) ++ ',':(show g) ++ ',':k ++ (insertSpaces b) ++ " (" ++ (show c) ++ ',':(show g) ++ ',':l ++ (insertSpaces d)
    show (Lx r@(Leaf a b c)) = (show a) ++ "[] --> 0 , " ++ b

data HGTree = HGT HGRule [HGTree] deriving (Show, Eq)

hgToTree :: HGTree -> Tree String
hgToTree (HGT r l) = Node (show r) (map hgToTree l)

printHG :: HGTree -> IO ()
printHG t = putStrLn $ drawTree $ hgToTree t

hgify :: PTree LIGRule -> HGTree
hgify (PT r EmptyContext) = HGT (Lx r) []
    -- if W2 is followed by empty context, it is trivial; you can remove the W2 and E
hgify (PT r cont) = let x = (mother $ conthead cont) in 
                      let y = (mother r) in
                    HGT (W2 x y) [contexthg cont y, HGT (Lx r) []]
    -- distinction between L rules and Lx rules is structural; all buds are Lx.
    -- do I ever need to reference what kind of rule each number is? eg Branch vs Leaf LIGrule?
    -- I don't think so, assuming that the LIG tree was well formed, ie. leaves only at leaves

emptycont :: TContext a -> Bool
emptycont EmptyContext = True
emptycont _ = False

conthead :: TContext LIGRule -> LIGRule
conthead EmptyContext = ligr0
conthead (TC m _ _ _) = m

contexthg :: TContext LIGRule -> VN -> HGTree
contexthg EmptyContext y = HGT (E y) []
    -- write a case (similar to hgify above) where if W1 is followed by empty context, it is trivial and remove it
contexthg (TC m@(Branch _ _ _ _ (Push i) _) l d r) y = let (t,b) = splitcon i [] d in 
    if emptycont t then 
        HGT (L m y) ((map hgify l) ++ (contexthg b y):(map hgify r))
    else 
        let x = mother $ conthead t 
            z = mother $ conthead b
        in HGT (L m y) ((map hgify l) ++ (HGT (W1 x y z i) [contexthg t z, contexthg b y]):(map hgify r))
contexthg (TC m l d r) y = HGT (L m y) ((map hgify l) ++ (contexthg d y):(map hgify r))

splitcon :: VI -> [VI] -> TContext LIGRule -> (TContext LIGRule, TContext LIGRule)
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

ligtohg :: LITree -> HGTree
ligtohg = hgify . petrify . parseRose

-- eg, try:
-- > latexTree $ hgToTree $ ligtohg tree2
-- > printTree $ hgToTree $ ligtohg tree2

-- strong equivalence translation
-- start with an algebraic function which evaluates a derivation tree

countnodes :: LITree -> Int
countnodes (LIT m d) = 1 + sum (map countnodes d)

measureHG :: LITree -> (LITree -> a) -> a
measureHG = undefined
