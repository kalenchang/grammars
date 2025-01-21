{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use concatMap" #-}
{-# HLINT ignore "Redundant bracket" #-}
module HGtoLIG where

import Prelude
import Data.Tree

-- nonterminals
data VN = S | T | B | C | D deriving (Eq, Show)

-- terminals
type VT = String

-- hg rules
data HGRule = Concat {mother :: VN, lefts :: [VN], daughter :: VN, rights :: [VN], label :: Int} 
        | Wrap {mother :: VN, left :: VN, right :: VN, label :: Int}
        | Leaf {mother :: VN, lterms :: [VT], rterms :: [VT], label :: Int} deriving Eq

insertSpaces :: Show a => [a] -> String
insertSpaces [] = ""
insertSpaces (x:xs) = ' ':(show x ++ insertSpaces xs)

insertSpaces' :: [String] -> String
insertSpaces' [] = ""
insertSpaces' (x:xs) = ' ':(x ++ insertSpaces' xs)

instance Show HGRule where
    show (Concat a b c d e) = show a ++ " -C" ++ show (length b + 1) ++ "->" ++ insertSpaces b ++ ' ':(show c) ++ insertSpaces d
    show (Wrap a b c d) = show a ++ " -W-> " ++ show b ++ ' ':(show c)
    show (Leaf a b c d) = show a ++ " -->" ++ insertSpaces' b ++ " ," ++ insertSpaces' c

-- hg grammars
newtype HG = HG ([VN], [VT], VN, [HGRule])

-- list of rules
hgr1, hgr2, hgr3, hgr4, hgr5, hgr6, hgr7 :: HGRule
hgr1 = Wrap S S C 1
hgr2 = Concat S [] T [] 2
hgr3 = Concat T [B] T [D] 3
hgr4 = Leaf T ["x"] ["y"] 4
hgr5 = Leaf B [] ["b"] 5
hgr6 = Leaf C [] ["c"] 6
hgr7 = Leaf D [] ["d"] 7

-- dummy rule
hgr0 :: HGRule
hgr0 = Leaf S [] [] 0

hgrlist :: [HGRule]
hgrlist = [hgr1, hgr2, hgr3, hgr4, hgr5, hgr6, hgr7]

lookupHGR :: Int -> [HGRule] -> HGRule
lookupHGR n (x:xs) = if label x == n then x else lookupHGR n xs
lookupHGR _ [] = hgr0

gethgrule :: Int -> HGRule
gethgrule x = lookupHGR x hgrlist

-- this HG produces b^n x c^m y d^n using wraps
hg1 :: HG
hg1 = HG ([S, T, B, C, D], ["x", "y", "b", "c", "d"], S, hgrlist)

data HGTree = HGT HGRule [HGTree] deriving (Show, Eq)

tree1 :: HGTree
tree1 = HGT hgr1 [
            HGT hgr2 [
                HGT hgr3 [
                    HGT hgr5 [],
                    HGT hgr4 [],
                    HGT hgr7 []
                ]
            ],
            HGT hgr6 []
        ]

yield :: HGTree -> (String, String)
yield (HGT (Leaf _ l r _) _) = (concat l, concat r)
yield (HGT (Concat _ l d r _) subtrees) = hgconcat l subtrees
yield (HGT (Wrap {}) [t1,t2]) = let (t1l, t1r) = yield t1 in let (t2l, t2r) = yield t2 in (t1l ++ t2l, t2r ++ t1r)

combine :: (String, String) -> String
combine (x,y) = x++y

hgconcat :: [a] -> [HGTree] -> (String, String)
hgconcat [] (t:ts) = let (d1, d2) = yield t in (d1, d2 ++ concat (map (combine . yield) ts))
hgconcat (l:ls) (t:ts) = let (s1, s2) = hgconcat ls ts in (combine (yield t) ++ s1, s2)

printTree :: Tree String -> IO ()
printTree t = putStrLn $ drawTree t

-- show an LIG tree using only its rule label
hgToLabelTree :: HGTree -> Tree String
hgToLabelTree (HGT r t) = Node (show $ label r) (map hgToLabelTree t)

-- show an LIG tree using the full rule
hgToRuleTree :: HGTree -> Tree String
hgToRuleTree (HGT r t) = Node (show r) (map hgToRuleTree t)

-- doesn't check for correctness, only takes mother node
hgToCatTree :: HGTree -> Tree String
hgToCatTree (HGT r t) = Node (show $ mother r) (map hgToCatTree t)

-- writes the LaTeX "forest" code to display the tree
latexTree :: Tree String -> IO ()
latexTree x = putStrLn $ unlines $ ("\\begin{forest}":(drawLatex x) ++ ["\\end{forest}"])

drawLatex :: Tree String -> [String]
drawLatex (Node x []) = lines ("[{"++x++"}]")
drawLatex (Node x ts0) = lines ("[{"++x++"}") ++ drawSubTrees ts0 ++ ["]"]
  where
    drawSubTrees [] = []
    drawSubTrees (t:ts) =
        zipWith (++) (repeat "    ") (drawLatex t) ++ drawSubTrees ts

-- HG derivations with only numbers
-- Cc Int:subscript index/designated daughter Int:rule number
data HGRN = Wp Int | Cc Int Int | Lx Int deriving (Eq, Show)

-- HG number tree
data HGNT = HGNT HGRN [HGNT]
treen1 :: HGNT
treen1 = HGNT (Wp 1) [
            HGNT (Cc 1 2) [
                HGNT (Cc 2 3) [
                    HGNT (Lx 5) [],
                    HGNT (Lx 4) [],
                    HGNT (Lx 7) []
                ]
            ],
            HGNT (Lx 6) []
        ]

treen11 :: HGNT
treen11 = HGNT (Cc 1 1) [
            HGNT (Cc 1 2) [
                HGNT (Cc 2 3) [
                    HGNT (Lx 5) [],
                    HGNT (Lx 4) [],
                    HGNT (Lx 7) []
                ]
            ],
            HGNT (Lx 6) []
        ]

treen2 :: HGNT
treen2 = HGNT (Wp 1) [
            HGNT (Wp 1) [
                HGNT (Cc 1 2) [
                    HGNT (Cc 2 3) [
                        HGNT (Lx 5) [],
                        HGNT (Lx 4) [],
                        HGNT (Lx 7) []
                    ]
                ],
                HGNT (Lx 6) []
            ],
            HGNT (Lx 6) []
        ]   

makeHGT :: HGNT -> HGTree
makeHGT (HGNT (Wp n) subtrees) = HGT (gethgrule n) (map makeHGT subtrees)
makeHGT (HGNT (Cc _ n) subtrees) = HGT (gethgrule n) (map makeHGT subtrees)
makeHGT (HGNT (Lx n) subtrees) = HGT (gethgrule n) (map makeHGT subtrees)

hgToTree :: HGNT -> Tree String
hgToTree (HGNT r l) = Node (show r) (map hgToTree l)

printHGT :: HGNT -> IO ()
printHGT t = putStrLn $ drawTree $ hgToTree t


----------------------------------------
-- LIG section

-- three kinds of rules in the new LIG
-- H are rules that come from HG (Cc, Wp, Lx)
-- Pop are rules that pop off the stack
-- Emp are rules which write empty string from alpha
data LIGR = HC Int Int | HW Int | HL Int | Pop | Emp deriving (Eq, Show)
data LITree = LIT LIGR [LITree] deriving (Eq, Show)

ligToTree :: LITree -> Tree String
ligToTree (LIT r l) = Node (show r) (map ligToTree l)

printLIGT :: LITree -> IO ()
printLIGT t = putStrLn $ drawTree $ ligToTree t

-- ligate
ligify :: HGNT -> LITree
ligify (HGNT (Lx n) subtrees) = LIT (HL n) [LIT Emp []]
ligify (HGNT (Cc m n) subtrees) = LIT (HC m n) (map ligify subtrees)
ligify (HGNT (Wp n) [l, r]) = LIT (HW n) [subtail (ligify l) (LIT Pop [ligify r])]

showLIGR :: LIGR -> String
showLIGR (HC a b) = undefined
showLIGR (HW a) = undefined
showLIGR (HL a) = let hgr = gethgrule a in (show $ mother hgr) ++ "[] ->" ++ (insertSpaces' (lterms hgr ++ rterms hgr))
showLIGR (Pop) = undefined
showLIGR (Emp) = "@[] -> "

-- instance Show LIGRule where
--     show (Branch a b c d e f) = let (s1, s2) = case e of {NoChange -> ("[..] ->","[..]"); 
--                                                           Push i -> ("[..] ->","[" ++ (show i) ++ "..]");
--                                                           Pop i -> ("[" ++ (show i) ++ "..] ->","[..]")} in
--             (show a) ++ s1 ++ (insertSpaces b) ++ ' ':(show c) ++ s2 ++ (insertSpaces d)
--     show (Leaf a b c) = (show a) ++ "[] ->" ++ (insertSpaces' b)

-- first is the one whose tail you are looking for; second is the tree to replace the tail
subtail :: LITree -> LITree -> LITree
subtail (LIT (HC m n) ts) r = let (a,b,c) = splitlist ts m in LIT (HC m n) (a ++ (subtail b r):c)
subtail (LIT rule [t]) r = LIT rule [subtail t r]
-- subtail (LIT (HW n) [t]) r = LIT (HW n) [subtail t r]
-- subtail (LIT Pop [t]) r = LIT Pop [subtail t r]
-- subtail (LIT (HL n) [t]) r = LIT (HL n) [subtail t r]
-- subtail (LIT Emp []) r = r
subtail (LIT _ []) r = r

splitlist :: [a] -> Int -> ([a], a, [a])
splitlist (l:ls) 1 = ([], l, ls)
splitlist (l:ls) n = let (a,b,c) = splitlist ls (n-1) in (l:a, b, c)

