module HG where

import Prelude
import Data.Tree
import Data.List (foldl')
import Control.Monad.State

import Printing

data HGRule nts ts = Concat {motherh :: nts, leftsh :: [nts], daughterh :: nts, rightsh :: [nts]} 
        | Wrap {motherh :: nts, lefth :: nts, righth :: nts}
        | Leafh {motherh :: nts, ltermsh :: [ts], rtermsh :: [ts]} deriving Eq

instance (Show nts, Show ts) => Show (HGRule nts ts) where
    show (Concat a b c d) = show a ++ " -C" ++ show (length b + 1) ++ "-> " ++ insertSpaces b ++ ' ':(show c) ++ insertSpaces d
    show (Wrap a b c) = show a ++ " -W-> " ++ show b ++ ' ':(show c)
    show (Leafh a b c) = show a ++ " --> " ++ concat (map show b) ++ ";" ++ concat (map show c)

instance (Texable nts, Texable ts) => Texable (HGRule nts ts) where
    texify (Concat a b c d) = texify a ++ " \\concar{" ++ show (length b + 1) ++ "} " ++ texifySpaces b ++ ' ':(texify c) ++ ' ':texifySpaces d
    texify (Wrap a b c) = texify a ++ " \\wrapar{} " ++ texify b ++ ' ':(texify c)
    texify (Leafh a b c) = texify a ++ " \\ra{} " ++ (stringSpaces (map texify b)) ++ "\\hgs{}" ++ (stringSpaces (map texify c))

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

combine2tex (x,y) = stringSpaces x ++ " \\hgs{}" ++  stringSpaces y

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

hgPresent (HGT (Leafh a b c) _) = Node (show a ++ "\n" ++ (concat b) ++ ';':(concat c)) []
hgPresent (HGT r@(Concat _ b _ _) t) = Node (case categoryh (HGT r t) of {Just cat -> show cat; Nothing -> "n/a"} ++ (show $ length b + 1)) (map hgPresent t)
hgPresent (HGT r@(Wrap _ _ _) t) = Node (case categoryh (HGT r t) of {Just cat -> show cat; Nothing -> "n/a"} ++ "W") (map hgPresent t)

-- show an HG tree using the full rule
-- hgtoRuleTree :: (Show nts, Show ts) => HGTree nts ts -> Tree String
hgtoRuleTree (HGT r l) = Node (show r) (map hgtoRuleTree l)

-- hgtoThreeTree :: (Show nts, Show ts, Eq nts) => HGTree nts ts -> Tree String
hgtoThreeTree t@(HGT r ts) = Node ((show r) ++ '\n':cat ++ ": " ++ (combine2 $ yieldh t)) (map hgtoThreeTree ts)
        where cat = case categoryh t of {Just cat -> show cat; Nothing -> "n/a"}

hgtoThreeLatex t@(HGT r ts) = Node ((texify r) ++ "\\\\\n" ++ cat ++ ": " ++ (combine2tex $ yieldh t)) (map hgtoThreeLatex ts)
        where cat = case categoryh t of {Just cat -> texify cat; Nothing -> "n/a"}


--------------------
-- hg4: swiss german/dutch cross-serial dependencies

hg4r1 = Concat CP [NP] VP []
hg4r2 = Wrap VP CP VE
hg4r3 = Concat VP [] VI []
hg4r4 = Leafh NP [] ["Jan"]
hg4r5 = Leafh NP [] ["Piet"]
hg4r6 = Leafh NP [] ["children"]
hg4r7 = Leafh VI [] ["swim"]
hg4r8 = Leafh VE [] ["help"]
hg4r9 = Leafh VE [] ["let"]

hg4t1 = HGT hg4r1 [
            HGT hg4r4 [],
            HGT hg4r2 [
                HGT hg4r1 [
                    HGT hg4r5 [],
                    HGT hg4r3 [
                        HGT hg4r7 []
                    ]
                ],
                HGT hg4r8 []
            ]
        ]



------------------------------
------- extended HGs ---------
------------------------------

data HGXRule nts ts = HGXR nts (HGO nts ts) deriving Eq

data HGO nts ts = LeafO [ts] [ts]
        | NTO nts
        | ConcatO [HGO nts ts] (HGO nts ts) [HGO nts ts]
        | WrapO [HGO nts ts] deriving Eq

instance (Show nts, Show ts) => Show (HGO nts ts) where
    show (LeafO x y) = concat (map show x) ++ ";" ++ concat (map show y)
    show (NTO x) = show x
    show (ConcatO b c d) = "C" ++ show (length b + 1) ++ "(" ++ insertCommas (b ++ c:d) ++ ")"
    show (WrapO xs) = "W(" ++ insertCommas xs ++ ")"

instance (Show nts, Show ts) => Show (HGXRule nts ts) where
    show (HGXR x op) = show x ++ " -> " ++ show op

instance (Texable nts) => Texable (HGO nts String) where
    texify (LeafO x y) = concat x ++ "\\hgs{}" ++ concat y
    texify (NTO x) = texify x
    texify (ConcatO b c d) = "\\fconc{" ++ show (length b + 1) ++ "}(" ++ texifyCommas (b ++ c:d) ++ ")"
    texify (WrapO xs) = "\\func{W}(" ++ texifyCommas xs ++ ")"

instance (Texable nts) => Texable (HGXRule nts String) where
    texify (HGXR x op) = texify x ++ " \\ra{} " ++ texify op

hgxr1 = HGXR S (ConcatO [] (WrapO [NTO B, NTO C, NTO T]) [LeafO ["a"] ["x"]])
hgxr2 = HGXR S (ConcatO [] (WrapO [LeafO ["b"] ["d"], NTO S]) [NTO S])
hgxr3 = HGXR S (LeafO [] [])

-- data HGXTree nts ts = HGXT (HGXRule nts ts) [HGXTree nts ts] deriving (Show, Eq)

hgxt1 = Node hgxr2 [Node hgxr3 [], Node hgxr2 [Node hgxr3 [], Node hgxr3 []]]
hgxt2 = Node hgxr2 [hgxt1, hgxt1]

-- yieldhx on trees
yieldhx (Node (HGXR nts o) ds) = fst $ runState (yieldhx' o) (map (yieldhx) ds)
-- yieldhx' on operations
yieldhx' :: (HGO nts ts) -> State [([ts],[ts])] ([ts],[ts])
yieldhx' (LeafO x y) = return (x,y)
yieldhx' (NTO x) = state (\(y:ys) -> (y, ys))
yieldhx' (ConcatO b c d) = state (\s -> let ((x1,y1),s1) = runState (foldl' (liftA2 conc2) (return ([],[])) (map yieldhx' b)) s in
        let ((x2,y2),s2) = runState (yieldhx' c) s1 in
            let ((x3,y3),s3) = runState (foldl' (liftA2 conc2) (return ([],[])) (map yieldhx' d)) s2 in
                ((x1++y1++x2,y2++x3++y3), s3))
    -- foldl' (liftA2 conc2) (return []) (map yieldhx' b) ++ fst c, snd c ++ foldl' (liftA2 conc2) (return []) (map yieldhx' d)
yieldhx' (WrapO xs) = foldl' (liftA2 wrap2) (return ([],[])) (map yieldhx' xs) 


conc2 = \(x1,x2) (y1,y2) -> (x1 ++ x2, y1 ++ y2)
wrap2 = \(x1,x2) (y1,y2) -> (x1 ++ y1, y2 ++ x2)

cathx (Node (HGXR nt o) ds) = if map Just (cathxnts o) == map cathx ds then Just nt else Nothing

cathxnts (LeafO _ _) = []
cathxnts (NTO x) = [x]
cathxnts (ConcatO b c d) = concatMap cathxnts (b ++ c:d)
cathxnts (WrapO xs) = concatMap cathxnts xs

hgxtoThreeTree t@(Node r ts) = Node ((show r) ++ '\n':cat ++ ": " ++ (combine2 $ yieldhx t)) (map hgxtoThreeTree ts)
        where cat = case cathx t of {Just cat -> show cat; Nothing -> "n/a"}

hgxtoThreeLatex t@(Node r ts) = Node ((texify r) ++ "\\\\\n" ++ cat ++ ": " ++ (combine2tex $ yieldhx t)) (map hgxtoThreeLatex ts)
        where cat = case cathx t of {Just cat -> texify cat; Nothing -> "n/a"}

