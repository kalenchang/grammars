module HG where

import Prelude
import TreePrint
import Data.Tree

data HGRule nts ts = Concat {motherh :: nts, leftsh :: [nts], daughterh :: nts, rightsh :: [nts]} 
        | Wrap {motherh :: nts, lefth :: nts, righth :: nts}
        | Leafh {motherh :: nts, ltermsh :: [ts], rtermsh :: [ts]} deriving Eq

instance (Show nts, Show ts) => Show (HGRule nts ts) where
    show (Concat a b c d) = show a ++ " -C" ++ show (length b + 1) ++ "-> " ++ insertSpaces b ++ ' ':(show c) ++ insertSpaces d
    show (Wrap a b c) = show a ++ " -W-> " ++ show b ++ ' ':(show c)
    show (Leafh a b c) = show a ++ " --> " ++ concat (map show b) ++ ";" ++ concat (map show c)

-- hg grammars
newtype HG = HG ([VN], [VT], VN, [HGRule VN VT])

-- list of rules
-- hgr1, hgr2, hgr3, hgr4, hgr5, hgr6, hgr7 :: HGRule VN VT
hgr1 = Wrap S S C
hgr2 = Concat S [] T []
hgr3 = Concat T [B] T [D]
hgr4 = Leafh T ["x"] ["y"]
hgr5 = Leafh B [] ["b"]
hgr6 = Leafh C [] ["c"]
hgr7 = Leafh D [] ["d"]

-- dummy rule
-- hgr0 :: HGRule VN VT
hgr0 = Leafh S [] []

-- hgrlist :: [HGRule VN VT]
hgrlist = [hgr1, hgr2, hgr3, hgr4, hgr5, hgr6, hgr7]

-- lookupHGR :: Int -> [HGRule VN VT] -> HGRule VN VT
-- lookupHGR n (x:xs) = if labelh x == n then x else lookupHGR n xs
-- lookupHGR _ [] = hgr0

-- gethgrule :: Int -> HGRule VN VT
-- gethgrule x = lookupHGR x hgrlist

-- this HG produces b^n x c^m y d^n using wraps
-- hg1 :: HG
hg1 = HG ([S, T, B, C, D], ["x", "y", "b", "c", "d"], S, hgrlist)

-- hgtree1 :: HGTree VN VT
hgtree1 = HGT hgr1 [
            HGT hgr2 [
                HGT hgr3 [
                    HGT hgr5 [],
                    HGT hgr4 [],
                    HGT hgr7 []
                ]
            ],
            HGT hgr6 []
        ]


--- Trees ---
data HGTree nts ts = HGT (HGRule nts ts) [HGTree nts ts] deriving (Show, Eq)

-- yieldh :: Show ts => HGTree nts ts -> ([ts], [ts])
yieldh (HGT (Leafh _ l r) _) = (l, r)
yieldh (HGT (Concat _ l d r) sub) = hgconcat l sub
yieldh (HGT (Wrap {}) [t1,t2]) = let (t1l, t1r) = yieldh t1 in let (t2l, t2r) = yieldh t2 in (t1l ++ t2l, t2r ++ t1r)

-- let n = length of [a], and concat all the terminals for the first n daughters, 
-- plus the left half of n+1; do the same on the other side
-- note to self: I think I need to pattern match on the empty list, in case of empty string (which I represent as [])
-- hgconcat :: Show ts => [a] -> [HGTree nts ts] -> ([ts], [ts])
hgconcat _ [] = ([],[])
hgconcat [] (t:ts) = let (d1, d2) = yieldh t in (d1, d2 ++ concat (map (combine . yieldh) ts))
hgconcat (l:ls) (t:ts) = let (s1, s2) = hgconcat ls ts in (combine (yieldh t) ++ s1, s2)

-- combine2 :: Show ts => ([ts], [ts]) -> String
combine2 (x,y) = concat (map show x)++';':concat (map show y)

-- show an HG tree using only its rule label
-- hgtoYieldTree :: Show ts => HGTree nts ts -> Tree String
hgtoYieldTree t@(HGT r ts) = Node (combine2 $ yieldh t) (map hgtoYieldTree ts)

-- categoryh :: Eq nts => (HGTree nts ts) -> Maybe nts
categoryh (HGT (Leafh a _ _) daughters) = if null daughters then Just a else Nothing
categoryh (HGT (Concat a b c d) daughters) = if and (zipWith checkcath daughters (b ++ c:d)) then Just a else Nothing       
categoryh (HGT (Wrap a b c) daughters) = case daughters of
                d1:d2:[] -> if checkcath d1 b && checkcath d2 c then Just a else Nothing
                _ -> Nothing
checkcath :: Eq nts => HGTree nts ts -> nts -> Bool
checkcath = \dt -> \n -> case categoryh dt of {Just x1 -> x1 == n; Nothing -> False}

-- hgtoCatTree :: (Show nts, Eq nts) => HGTree nts ts -> Tree String
hgtoCatTree (HGT r t) = Node (case categoryh (HGT r t) of {Just cat -> show cat; Nothing -> "n/a"}) (map hgtoCatTree t)

-- show an HG tree using the full rule
-- hgtoRuleTree :: (Show nts, Show ts) => HGTree nts ts -> Tree String
hgtoRuleTree (HGT r l) = Node (show r) (map hgtoRuleTree l)

-- hgtoAllTree :: (Show nts, Show ts, Eq nts) => HGTree nts ts -> Tree String
hgtoAllTree t@(HGT r ts) = Node ((show r) ++ '\n':cat ++ ": " ++ (combine2 $ yieldh t)) (map hgtoAllTree ts)
        where cat = case categoryh t of {Just cat -> show cat; Nothing -> "n/a"}
