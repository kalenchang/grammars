{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use concatMap" #-}
{-# HLINT ignore "Redundant bracket" #-}
module HGtoLIG where

import Prelude
import Data.Tree
import TreePrint
import HG
import LIG

-- show an HG tree using only its rule label
-- hgtoLabelTree :: HGTree -> Tree String
-- hgtoLabelTree (HGT r t) = Node (show $ label r) (map hgtoLabelTree t)

-- doesn't check for correctness, only takes mother node
-- hgtoLeftTree :: HGTree -> Tree String
-- hgtoLeftTree (HGT (Leaf a b c _) t) = Node (show a ++ '\n':b ++ ',':c) (map hgtoLeftTree t)
-- hgtoLeftTree (HGT r t) = Node (show $ mother r) (map hgtoLeftTree t)

-- HG derivations with only numbers
-- Cc Int:subscript index/designated daughter Int:rule number
-- data HGRN = Wp Int | Cc Int Int | Lx Int deriving (Eq, Show)

-- HG number tree
-- data HGNT = HGNT HGRN [HGNT]
-- treen1 :: HGNT
-- treen1 = HGNT (Wp 1) [
--             HGNT (Cc 1 2) [
--                 HGNT (Cc 2 3) [
--                     HGNT (Lx 5) [],
--                     HGNT (Lx 4) [],
--                     HGNT (Lx 7) []
--                 ]
--             ],
--             HGNT (Lx 6) []
--         ]

-- treen11 :: HGNT
-- treen11 = HGNT (Cc 1 1) [
--             HGNT (Cc 1 2) [
--                 HGNT (Cc 2 3) [
--                     HGNT (Lx 5) [],
--                     HGNT (Lx 4) [],
--                     HGNT (Lx 7) []
--                 ]
--             ],
--             HGNT (Lx 6) []
--         ]

-- treen2 :: HGNT
-- treen2 = HGNT (Wp 1) [
--             HGNT (Wp 1) [
--                 HGNT (Cc 1 2) [
--                     HGNT (Cc 2 3) [
--                         HGNT (Lx 5) [],
--                         HGNT (Lx 4) [],
--                         HGNT (Lx 7) []
--                     ]
--                 ],
--                 HGNT (Lx 6) []
--             ],
--             HGNT (Lx 6) []
--         ]   

-- makeHGT :: HGNT -> HGTree
-- makeHGT (HGNT (Wp n) subtrees) = HGT (gethgrule n) (map makeHGT subtrees)
-- makeHGT (HGNT (Cc _ n) subtrees) = HGT (gethgrule n) (map makeHGT subtrees)
-- makeHGT (HGNT (Lx n) subtrees) = HGT (gethgrule n) (map makeHGT subtrees)

-- hgToTree :: HGNT -> Tree String
-- hgToTree (HGNT r l) = Node (show r) (map hgToTree l)

-- printHGT :: HGNT -> IO ()
-- printHGT t = putStrLn $ drawTree $ hgToTree t


----------------------------------------
-- LIG section

-- need to add a new type for the nonterminals of LIGs derived from HGs
-- Alpha is alpha, N are the nonterminals from the original HG
-- T represents terminals from the original HG -- they can serve as unary rules to write just the terminal
-- -- this is because for the lexical rules in the LIG I want to mix Ts and NTs, so this is a workaround
data LIGtransNT nts ts = Alpha | Nl nts | Tl ts deriving Eq

instance (Show nts, Show ts) => Show (LIGtransNT nts ts) where
    show Alpha = "@"
    show (Nl n) = show n
    show (Tl t) = '!':show t

-- three kinds of rules in the new LIG
-- H are rules that come from HG (HC = concat, HW = wrap, HL = lexical)
-- Pop are rules that pop off the stack (top down)
-- Emp are rules which write empty string from alpha
-- Unary are rules which rewrite a NT named after a terminal as that terminal
-- data LIGR = HC Int Int | HW Int | HL Int | Pop | Emp deriving (Eq, Show)
-- makeHCrule :: (HGRule nts ts) -> LIGRule (LIGtransNT nts ts) ts nts
makeHCrule (Concat a b c d e) = Branch (Nl a) (map Nl b) (Nl c) (map Nl d) NoChange e

-- makeHWrule :: (HGRule nts ts) -> LIGRule (LIGtransNT nts ts) ts nts
makeHWrule (Wrap a b c d) = Branch (Nl a) [] (Nl b) [] (Push c) d

-- makeHLrule :: (HGRule nts ts) -> LIGRule (LIGtransNT nts ts) ts nts
makeHLrule (Leafh a b c d) = Branch (Nl a) (map Tl b) Alpha (map Tl c) NoChange d

-- makePoprule :: nts -> LIGRule (LIGtransNT nts ts) ts nts
makePoprule c = Branch Alpha [] (Nl c) [] (Pop c) 1

-- emprule :: LIGRule (LIGtransNT nts ts) ts nts
emprule = Leaf Alpha [] 2 

-- makeUnaryrule :: ts -> LIGRule (LIGtransNT nts ts) ts nts
makeUnaryrule c = Leaf (Tl c) [c] 3

-- ligToTree :: LITree -> Tree String
-- ligToTree (LIT r l) = Node (show r) (map ligToTree l)

-- printLIGT :: LITree -> IO ()
-- printLIGT t = putStrLn $ drawTree $ ligToTree t

-- ligate
-- ligify :: HGTree nts ts -> LITree (LIGtransNT nts ts) ts nts
ligify (HGT rule@(Leafh _ b c _) []) = LIT (makeHLrule rule) ((map ((\x -> LIT x []) . makeUnaryrule) b) 
                                                            ++ (LIT emprule []):(map ((\x -> LIT x []) . makeUnaryrule) c))
ligify (HGT rule@(Concat _ _ _ _ _) subtrees) = LIT (makeHCrule rule) (map ligify subtrees)
ligify (HGT rule@(Wrap _ _ c _) [l, r]) = LIT (makeHWrule rule) [subtail (ligify l) (LIT (makePoprule c) [ligify r])]

-- showLIGR :: LIGR -> String
-- showLIGR (HC a b) = undefined
-- showLIGR (HW a) = undefined
-- showLIGR (HL a) = let hgr = gethgrule a in (show $ mother hgr) ++ "[] -> " ++ lterms hgr ++ " " ++ rterms hgr
-- showLIGR (Pop) = undefined
-- showLIGR (Emp) = "@[] -> "

-- instance Show LIGRule where
--     show (Branch a b c d e f) = let (s1, s2) = case e of {NoChange -> ("[..] ->","[..]"); 
--                                                           Push i -> ("[..] ->","[" ++ (show i) ++ "..]");
--                                                           Pop i -> ("[" ++ (show i) ++ "..] ->","[..]")} in
--             (show a) ++ s1 ++ (insertSpaces b) ++ ' ':(show c) ++ s2 ++ (insertSpaces d)
--     show (Leaf a b c) = (show a) ++ "[] ->" ++ (insertSpaces' b)

-- first is the one whose tail you are looking for; second is the tree to replace the tail
-- subtail :: LITree nts ts ind -> LITree nts ts ind -> LITree nts ts ind 
subtail (LIT rule@(Branch _ b _ _ _ _) ts) r = let (x,y,z) = splitlist ts (length b) in LIT rule (x ++ (subtail y r):z)
subtail (LIT rule [t]) r = LIT rule [subtail t r]
-- subtail (LIT (HW n) [t]) r = LIT (HW n) [subtail t r]
-- subtail (LIT Pop [t]) r = LIT Pop [subtail t r]
-- subtail (LIT (HL n) [t]) r = LIT (HL n) [subtail t r]
-- subtail (LIT Emp []) r = r
subtail (LIT _ []) r = r

-- splitlist splits the first argument into a triple at the position indicated by the second argument
-- makes a true "headed" list
-- splitlist :: [a] -> Int -> ([a], a, [a])
splitlist (l:ls) 0 = ([], l, ls)
splitlist (l:ls) n = let (x,y,z) = splitlist ls (n-1) in (l:x, y, z)


-- try:
-- > latexTree $ ligtoAllTree $ ligify hgtree1

--------------------------
---- example grammars ----
-- hg1: w v wR vR

hg1r1 = Concat S [A] T [] 1
hg1r2 = Wrap T S A 2
hg1r3 = Concat S [C] U [] 3
hg1r4 = Wrap U S C 4
hg1r5 = Concat S [] V [] 5
hg1r6 = Concat V [B] V [B] 6
hg1r7 = Concat V [D] V [D] 7
hg1r8 = Leafh V [] [] 8
hg1r9 = Leafh A ["a"] [] 9
hg1r10 = Leafh B ["b"] [] 10
hg1r11 = Leafh C ["c"] [] 11
hg1r12 = Leafh D ["d"] [] 12

-- string: acc bbdd , cca ddbb
hg1t1 = HGT hg1r1 [
            HGT hg1r9 [],
            HGT hg1r2 [
                HGT hg1r3 [
                    HGT hg1r11 [],
                    HGT hg1r4 [
                        HGT hg1r3 [
                            HGT hg1r11 [],
                            HGT hg1r4 [
                                HGT hg1r5 [
                                    HGT hg1r6 [
                                        HGT hg1r10 [],
                                        HGT hg1r6 [
                                            HGT hg1r10 [],
                                            HGT hg1r7 [
                                                HGT hg1r12 [],
                                                HGT hg1r7 [
                                                    HGT hg1r12 [],
                                                    HGT hg1r8 [],
                                                    HGT hg1r12 []
                                                ],
                                                HGT hg1r12 []
                                            ],
                                            HGT hg1r10 []
                                        ],
                                        HGT hg1r10 []
                                    ]
                                ],
                                HGT hg1r11 []
                            ]
                        ],
                        HGT hg1r11 []
                    ]
                ],
                HGT hg1r9 []
            ]
        ]

