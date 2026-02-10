module LIG where

import Prelude
import Data.Tree
import Data.Maybe ( isJust, fromJust )

import Printing

-- indices
type VI = Int

-- stack change
data SC ind = NoChange | Push ind | Pop ind deriving (Show, Eq)

-- two kinds of LIG rules: Branch node or a Leaf node
-- Branch: 1 rewrites as 2 3 4, where 3 is the distinguished daughter, with stack change 5
-- Leaf: 1 rewrites as 2
-- data LIGRule = Branch VN [VN] VN [VN] SC Int | Leaf VN [VT] Int deriving (Show, Eq)

data LIGRule nts ts ind = Branch {mother :: nts, lefts :: [nts], daughter :: nts, rights :: [nts], change :: SC ind} 
        | Leaf {mother :: nts, terms :: [ts]} deriving Eq

-- i'm starting to feel like branch rules and leaf rules should be their own kinds of rules... but idk
-- data LIGRule = Branch LIGBranchRule | Leaf LIGLeafRule deriving (Show, Eq)

-- data LIGBranchRule = LIGBranchRule {mother :: VN, lefts :: [VN], daughter :: VN, rights :: [VN], change :: SC, label :: Int} deriving (Show, Eq)
-- data LIGLeafRule = LIGLeafRule {mother :: VN, terms :: [VT], label :: Int} deriving (Show, Eq)


instance (Show nts, Show ts, Show ind) => Show (LIGRule nts ts ind) where
    show (Branch a b c d e) = let (s1, s2) = case e of {NoChange -> ("[] ->","[]"); 
                                                          Push i -> ("[] ->","[" ++ (show i) ++ "]");
                                                          Pop i -> ("[" ++ (show i) ++ "] ->","[]")} in
            (show a) ++ s1 ++ (insertSpaces b) ++ ' ':(show c) ++ s2 ++ (insertSpaces d)
    show (Leaf a b) = (show a) ++ "[] -> " ++ concat (map show b)

instance (Texable nts, Texable ts, Texable ind) => Texable (LIGRule nts ts ind) where
    texify (Branch a b c d e) = let (s1, s2) = case e of {NoChange -> ("[] \\ra{} ","[] "); 
                                                          Push i -> ("[] \\ra{} ","[" ++ (texify i) ++ "] ");
                                                          Pop i -> ("[" ++ (texify i) ++ "] \\ra{} ","[] ")} in
            texify a ++ s1 ++ texifySpaces b ++ ' ':(texify c) ++ s2 ++ texifySpaces d
    texify (Leaf a b) = (texify a) ++ "[] \\ra{} " ++ texifySpaces b

newtype LIG = LIG ([VN], [VT], [VI], VN, [LIGRule VN VT VI])

-- list of rules
-- ligr1, ligr2, ligr3, ligr4, ligr5, ligr6, ligr7, ligr8, ligr9, ligr10, ligr0 :: LIGRule VN VT VI
ligr1 = Branch S [A] S [] (Push 1)
ligr2 = Branch S [] T [] NoChange 
ligr3 = Branch T [B] T [D] NoChange
ligr4 = Branch T [] U [] NoChange
ligr5 = Branch U [] U [C] (Pop 1)
ligr6 = Leaf U []
ligr7 = Leaf A ["a"]
ligr8 = Leaf B ["b"]
ligr9 = Leaf C ["c"]
ligr10 = Leaf D ["d"] 
-- dummy rule
ligr0 = Branch S [] T [] NoChange

-- ligrlist :: [LIGRule VN VT VI]
ligrlist = [ligr1, ligr2, ligr3, ligr4, ligr5, ligr6, ligr7, ligr8, ligr9, ligr10]

-- lookupLIGR :: Int -> [LIGRule VN VT VI] -> LIGRule VN VT VI
-- lookupLIGR n (x:xs) = if label x == n then x else lookupLIGR n xs
-- lookupLIGR _ [] = ligr0

-- getrule :: Int -> LIGRule VN VT VI
-- getrule x = lookupLIGR x ligrlist


---- Trees ----
data LITree nts ts ind = LIT (LIGRule nts ts ind) [LITree nts ts ind] deriving (Show, Eq)
-- is it possible/better to just use Tree LIGRule?

-- changeStack tries to do the stackchange on the given stack, returns Nothing if not possible
-- changeStack assumes you are working top down, so a Push i rule has the designate daughter's stack
--   one longer than the mother's
-- changeStack :: Eq ind => SC ind -> Maybe [ind] -> Maybe [ind]
changeStack _ Nothing = Nothing
changeStack NoChange s = s
changeStack (Push i) (Just s) = Just (i:s)
changeStack (Pop i) (Just []) = Nothing
changeStack (Pop i) (Just (x:s)) = if x == i then Just s else Nothing

-- stackUp does the same thing as changeStack, except working bottom up
-- stackUp :: Eq ind => SC ind -> Maybe [ind] -> Maybe [ind]
stackUp _ Nothing = Nothing
stackUp NoChange s = s
stackUp (Pop i) (Just s) = Just (i:s)
stackUp (Push i) (Just []) = Nothing
stackUp (Push i) (Just (x:s)) = if x == i then Just s else Nothing

-- given 3 arguments, l, r, s, where s is a list of b
-- returns a list of lists of b, where s is the len(l)+1th item of the list,
-- with len(l) and len(r) empty stacks to the left and right of s
-- use case: pass the stack to the designated daughter, and all other daughters get empty stacks
-- stackLister :: [a] -> [a] -> [b] -> [[b]]
stackLister l r s = map (\x -> []) l ++ s:(map (\x -> []) r)

-- check whether a tree produces the given category
-- still need to check whether stack clears
-- produces :: (Eq nts, Eq ind) => (LITree nts ts ind) -> nts -> [ind] -> Bool
produces (LIT (Branch a b c d e) daughters) nt stack = let newStack = changeStack e (Just stack) in
    a == nt && isJust newStack && and (zipWith3 produces daughters (b ++ c:d) (stackLister b d (fromJust newStack)))
produces (LIT (Leaf a b) daughters) nt stack = a == nt && null stack && null daughters
    -- ignore b (list of terminals) since it doesn't affect whether derivation is valid
-- produces _ _ _ = False
    -- adding a catchall (for now)... unsure if needed

-- extract :: Int -> [a] -> (a,[a])
extract _ [] = undefined
extract i (x:xs) = removeIndex i (x,xs)
    where
        -- removeIndex :: Int -> (a,[a]) -> (a,[a])
        removeIndex _ (x,[]) = (x,[])
        removeIndex i (x,y:ys) = if i == 0 then (x,y:ys) else let (z,zs) = (removeIndex (i-1) (y,ys)) in (z, x:zs)

-- another alternative to produces: category :: LITree -> Maybe (VN, [VI])
-- category of a tree is either a NT + stack, or it's nothing if the tree is invalid
-- category :: (Eq nts, Eq ind) => (LITree nts ts ind) -> Maybe (nts, [ind])
category (LIT (Leaf a _) daughters) = if null daughters then Just (a, []) else Nothing
category (LIT (Branch a b c d e) daughters) = if correctDaughters && isJust newStack then Just (a, fromJust newStack) else Nothing
    where
        (desig,rest) = extract (length b) daughters
        correctDaughters = and (zipWith checksides rest (b ++ d)) && checkmiddle 
        -- dt = daughter, n = nonterminal, s = stack
        checksides = \dt -> \n -> case category dt of {Just (x1, x2) -> x1 == n && x2 == []; Nothing -> False}
        checkmiddle = case category desig of {Just (x1, x2) -> x1 == c; Nothing -> False}
        newStack = case category desig of {Just (x1, x2) -> stackUp e (Just x2); Nothing -> Nothing}

-- mytree1 :: LITree
-- mytree1 = Bin ligr4 (Lef ligr7) (Bin ligr1 (Lef ligr8) (Lef ligr7))

-- tree1 :: LITree VN VT VI
tree1 = LIT ligr2 [LIT ligr4 [LIT ligr6 []]]

-- tree2 :: LITree VN VT VI
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

-- tree3 :: LITree VN VT VI
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

-- tree4 :: LITree VN VT VI
tree4 = LIT ligr2 [
            LIT ligr3 [
                LIT ligr8 [],
                LIT ligr4 [
                    LIT ligr6 []
                ],
                LIT ligr10 []
            ]
        ]

-- isSentence :: LITree VN VT VI -> Bool
isSentence tree = produces tree S []

-- yield :: Show ts => LITree nts ts ind -> [ts]
yield (LIT (Leaf a b) d) = b
yield (LIT (Branch a b c d e) daughters) = concat (map yield daughters)

-- show an LIG tree using only its rule label
-- ligtoLabelTree :: LITree nts ts ind -> Tree String
-- ligtoLabelTree (LIT r t) = Node (show $ label r) (map ligtoLabelTree t)

-- show an LIG tree using the full rule
-- ligtoRuleTree :: (Show nts, Show ts, Show ind) => LITree nts ts ind -> Tree String
ligtoRuleTree (LIT r t) = Node (show r) (map ligtoRuleTree t)

-- printTree :: Tree String -> IO ()
-- printTree t = putStrLn $ drawTree t

-- doesn't show stack; only shows the left side of each rule as the node
-- technically Leaf nodes should not have any daughters, so t in the Leaf line should be []
-- but also nothing in the data structure is stopping Leaf from having daughters
-- ligtoLeftsTree :: (Show nts, Show ts) => LITree nts ts ind -> Tree String
ligtoLeftsTree (LIT (Leaf a b) t) = Node (show a ++ '\n':(show b)) (map ligtoLeftsTree t)
ligtoLeftsTree (LIT r t) = Node (show $ mother r) (map ligtoLeftsTree t)

-- shows tree in a presentation friendly way: category+stack and terminals only (assumes b :: list of strings)
ligPresent (LIT (Leaf a b) t) = Node (show a ++ "[]\n" ++ (concat b)) []
ligPresent (LIT r t) = Node (case category (LIT r t) of {Just (cat,stack) -> show cat ++ show stack; Nothing -> "n/a"}) (map ligPresent t)

-- shows the category of the subtree as indicated by the `category' function
-- ought to implement some kind of memoization so it does not need to calculate the subtree's categories multiple times
-- ligtoCatTree :: (Show nts, Eq nts, Show ind, Eq ind) => LITree nts ts ind -> Tree String
ligtoCatTree (LIT r t) = Node (case category (LIT r t) of {Just (cat,stack) -> show cat ++ show stack; Nothing -> "n/a"}) (map ligtoCatTree t)

-- shows the yield so far at each node
-- ligtoYieldTree :: Show ts => LITree nts ts ind -> Tree String
ligtoYieldTree t@(LIT r ts) = Node (concat (map show (yield t))) (map ligtoYieldTree ts)

-- shows the rule on one line, second line is cat: yield
-- ligtoAllTree :: (Show nts, Show ts, Eq nts, Show ind, Eq ind) => LITree nts ts ind -> Tree String
ligtoAllTree t@(LIT r ts) = Node ((show r) ++ '\n':cat ++ ": " ++ (concat (map show (yield t)))) (map ligtoAllTree ts)
        where cat = case category t of {Just (cat,stack) -> show cat ++ show stack; Nothing -> "n/a"}

-- ligtoAllLatex :: (Texable nts, Texable ts, Eq nts, Texable ind, Eq ind) => LITree nts ts ind -> Tree String
ligtoAllLatex t@(LIT r ts) = Node ((texify r) ++ "\\\\\n" ++ cat ++ ": " ++ (texifySpaces (yield t))) (map ligtoAllLatex ts)
        where cat = case category t of {Just (cat,stack) -> texify cat ++ texify stack; Nothing -> "n/a"}

ligtoTwoTree t@(LIT r ts) = Node ((show r) ++ '\n':cat ) (map ligtoTwoTree ts)
        where cat = case category t of {Just (cat,stack) -> show cat ++ show stack; Nothing -> "n/a"}


lig2r1 = Branch S [A] S [] (Push 1)
lig2r2 = Branch S [B] S [] (Push 2)
lig2r3 = Branch S [] T [] NoChange 
lig2r4 = Branch T [A] T [] (Pop 1)
lig2r5 = Branch T [B] T [] (Pop 2)
lig2r6 = Leaf T [""]
lig2r7 = Leaf A ["a"]
lig2r8 = Leaf B ["b"]

lig2t2 = LIT lig2r1 [
            LIT lig2r7 [],
            LIT lig2r2 [
                LIT lig2r8 [],
                LIT lig2r2 [
                    LIT lig2r8 [],
                    LIT lig2r3 [
                        LIT lig2r5 [
                            LIT lig2r8 [],
                            LIT lig2r5 [
                                LIT lig2r8 [],
                                LIT lig2r4 [
                                    LIT lig2r7 [],
                                    LIT lig2r6 [
                                    ]
                                ]
                            ]
                        ]
                    ]
                ]
            ]
        ]


lig3r1 = Branch S [A] S [] (Push 1)
lig3r2 = Branch S [B] S [] (Pop 1)
lig3r3 = Leaf S [""]
lig3r4 = Leaf A ["a"]
lig3r5 = Leaf B ["b"]

lig3t1 = LIT lig3r1 [
            LIT lig3r4 [],
            LIT lig3r1 [
                LIT lig3r4 [],
                LIT lig3r2 [
                    LIT lig3r5 [],
                    LIT lig3r1 [
                        LIT lig3r4 [],
                        LIT lig3r2 [
                            LIT lig3r5 [],
                            LIT lig3r2 [
                                LIT lig3r5 [],
                                LIT lig3r3 [
                                ]
                            ]
                        ]
                    ]
                ]
            ]
        ]

lig3t2 = LIT lig3r1 [
            LIT lig3r4 [],
            LIT lig3r1 [
                LIT lig3r4 [],
                LIT lig3r2 [
                    LIT lig3r5 [],
                    LIT lig3r1 [
                        LIT lig3r4 [],
                        LIT lig3r2 [
                            LIT lig3r5 [],
                            LIT lig3r2 [
                                LIT lig3r5 [],
                                LIT lig3r1 [
                                    LIT lig3r4 [],
                                    LIT lig3r2 [
                                        LIT lig3r5 [],
                                        LIT lig3r3 []
                                    ]
                                ]
                            ]
                        ]
                    ]
                ]
            ]
        ]

-------------------
-- lig4: multiple wh-movement

lig4r1 = Branch VP [] VT [DP] (NoChange)
lig4r2 = Branch VP [] VT [DPT] (Pop I)
lig4r2H = Branch VP [] VT [DPT] (Pop Hum)
lig4r2N = Branch VP [] VT [DPT] (Pop Non)
lig4r3 = Branch VP [VE] CP [] (NoChange)
lig4r4 = Branch CP [DP] VP [] (NoChange)
lig4r5 = Branch CP [DPT] VP [] (Pop I)
lig4r5H = Branch CP [DPT] VP [] (Pop Hum)
lig4r5N = Branch CP [DPT] VP [] (Pop Non)
lig4r6 = Branch CP [WH] CP [] (Push I)
lig4r6H = Branch CP [WHH] CP [] (Push Hum)
lig4r6N = Branch CP [WHN] CP [] (Push Non)

lig4r7 x = Leaf DP [x]
lig4r8 x = Leaf VT [x]
lig4r9 x = Leaf VE [x]
lig4r10 x = Leaf WH [x]
-- lig4r10 = Leaf WH ["who"]
lig4r10H = Leaf WHH ["who"]
lig4r10N = Leaf WHN ["what"]
lig4r11 = Leaf DPT ["\\ml{t}"]

lig4r7j = Leaf DP ["John"]
lig4r7m = Leaf DP ["Mary"]
lig4r8s = Leaf VT ["saw"]
lig4r8b = Leaf VT ["met"]
lig4r9s = Leaf VE ["say"]
lig4r9k = Leaf VE ["know"]

-- John saw Mary
lig4t1 :: LITree VN VT VII
lig4t1 = LIT lig4r4 [
            LIT (lig4r7 "John") [],
            LIT lig4r1 [
                LIT (lig4r8 "saw") [],
                LIT (lig4r7 "Mary") []
            ]
        ]

-- what John say who Mary know t saw t
lig4t2 = LIT lig4r6 [
            LIT (lig4r10 "what") [],
            LIT lig4r4 [
                LIT (lig4r7 "John") [],
                LIT lig4r3 [
                    LIT (lig4r9 "say") [],
                    LIT lig4r6 [
                        LIT (lig4r10 "who") [],
                        LIT lig4r4 [
                            LIT (lig4r7 "Mary") [],
                            LIT lig4r3 [
                                LIT (lig4r9 "know") [],
                                LIT lig4r5 [
                                    LIT lig4r11 [],
                                    LIT lig4r2 [
                                        LIT (lig4r8 "saw") [],
                                        LIT lig4r11 []
                                    ]
                                ]
                            ]
                        ]
                    ]
                ]
            ]
        ]
