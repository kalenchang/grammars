module PDA where

import Prelude hiding ((^))
import Data.Tree
import Data.Maybe
import Data.List (foldl')

import Printing
import Lambdas

data Stacksymb = Y | Z deriving (Eq, Show)

-- top of stack is left (outermost element on list)
data PDATrans st sy ind = PDAT {fromState :: st, symb :: sy, popInd :: [ind], toState :: st, pushInd :: [ind]} deriving Eq
-- I think I want to keep symb as [sy] so that I have a 0 element for general sy, not just strings?
-- or make it monoidal?

instance (Show st, Show sy, Show ind) => Show (PDATrans st sy ind) where
    show (PDAT a b c d e) = '(':show a ++ ',':show b ++ ',':show c ++ ") -> (" ++ show d ++ ',': show e ++")"

instance (Show st, Show ind) => Texable (PDATrans st String ind) where
    texify (PDAT a b c d e) = showstate a ++ showstack c ++ " \\xra{" ++ b ++ "} " ++ showstate d ++ showstack e

showstate :: (Show a) => a -> String
showstate = \x -> let out = show x in if out == "()" then "\\ap" else out

showstack :: (Show a) => [a] -> String
showstack s = "[" ++ concatMap show s ++ "]"

-- -- old pdarun type, a cons list
-- data PDANur st sy ind = EndNur st [ind] | PDAN (PDATrans st sy ind) (PDANur st sy ind) deriving Eq

-- -- new pdarun type, a snoc list
-- data PDARun st sy ind = StartRun st [ind] | PDAR (PDARun st sy ind) (PDATrans st sy ind) deriving Eq

-- instance (Show st, Show sy, Show ind) => Show (PDARun st sy ind) where
--     show (PDAR trans rest) = show trans ++ '\n':show rest

pdat1 = PDAT 1 "a" [Z] 1 [Z, Z]
pdat2 = PDAT 1 "" [Z] 2 []
pdat3 = PDAT 2 "b" [Z] 2 []

-- -- old pdarun structure
-- pdan1 = PDAN pdat1 (
--             PDAN pdat1 (
--                 PDAN pdat2 (
--                     PDAN pdat3 (
--                         PDAN pdat3 (EndNur 2 [])
--                     )
--                 )
--             )
--         )

-- -- new pdarun structure
-- pdar1 = PDAR (
--             PDAR (
--                 PDAR (
--                     PDAR (
--                         PDAR (
--                             StartRun 1 [Z]
--                             ) pdat1
--                         ) pdat1
--                     ) pdat2
--                 ) pdat3
--             ) pdat3

-- list structure
pdal1 = [pdat1, pdat1, pdat1, pdat2, pdat3, pdat3, pdat3]
pdalr1 = (1, [Z], pdal1)

-- old
-- pdar2 = PDAR pdat1 (
--             PDAR pdat1 (
--                 PDAR pdat1 (
--                     PDAR pdat2 (
--                         PDAR pdat3 (
--                             PDAR pdat3 (
--                                 PDAR pdat3 (EndRun 2)
--                             )
--                         )
--                     )
--                 )
--             )
--         )

-- new pdarun structure
-- pdar2 = PDAR (
--             PDAR (
--                 PDAR (
--                     PDAR (
--                         PDAR (
--                             PDAR (
--                                 PDAR (
--                                     StartRun 1 [Z]
--                                     ) pdat1
--                                 ) pdat1
--                             ) pdat1
--                         ) pdat2
--                     ) pdat3
--                 ) pdat3
--             ) pdat3

pda2t1 = PDAT 1 "Mary " [S] 1 [S, V]
pda2t2 = PDAT 1 "John " [S] 1 [S, V]
pda2t3 = PDAT 1 "swim " [S, V] 1 []
pda2t4 = PDAT 1 "let " [V] 1 []

mupda2list = [(pda2t1, x ^ x # mary'),
        (pda2t2, x ^ x # john'),
        (pda2t3, x ^ x # swim'),
        (pda2t4, x ^ x # let')]
mupda2 = lookupint mupda2list
iotapda2 = idterm

pda2lr1 = [pda2t1, pda2t2, pda2t3, pda2t4]

-- pdar11 = PDAR (
--             PDAR (
--                 PDAR (
--                     PDAR (
--                         PDAR (
--                             StartRun 1 [Z]
--                             ) pdat11
--                     ) pdat11
--                 ) pdat12
--             ) pdat13
--         ) pdat13

-- takes index i off of top of stack s
-- stripind :: Eq a => a -> Maybe [a] -> Maybe [a]
stripind i s = do
            x:xs <- s
            if x == i then (Just xs) else Nothing

-- adds list of indices l to top of stack s
-- addind :: [a] -> Maybe [a] -> Maybe [a]
addind l s = do
        xs <- s
        return (l ++ xs)

-- -- need to clean up all the maybes......
-- toWhere :: (Eq st, Eq ind) => PDARun st sy ind -> Maybe (st, [ind])
-- toWhere (StartRun s st) = Just (s, st)
-- toWhere (PDAR rest t@(PDAT a _ c d e)) = do
--                                             (state, stack) <- toWhere rest
--                                             newstack <- addind e (stripind c (Just stack))
--                                             if state == a then Just (d, newstack) else Nothing

    
    -- case (toWhere rest) of {Just (state, stack) -> if state == a then
    --                 case addind e (stripind c (Just stack)) of {Just newstack -> Just (d, newstack); Nothing -> Nothing} else Nothing;
    --                 Nothing -> Nothing}

-- yieldp (StartRun _ _) = []
-- yieldp (PDAR rest (PDAT _ b _ _ _)) = (yieldp rest) ++ [b]

-- pdatoAllTree (StartRun s st) = Node (show s ++ show st) []
-- pdatoAllTree r@(PDAR rest t) = Node ((show t) ++ '\n':cat ++ ": " ++ (concat (yieldp r))) [pdatoAllTree rest]
--         where cat = case toWhere r of {Just (cat,stack) -> show cat ++ show stack; Nothing -> "n/a"}
-- -- as written this tree is upside down: the start state is at the bottom of the tree and the path proceeds upward

invertlinTree :: Tree a -> ([Tree a] -> [Tree a]) -> Tree a
invertlinTree (Node n []) tc = (Node n (tc []))
invertlinTree (Node n (x:xs)) tc = invertlinTree x (\k -> [Node n (tc k)])
invlin t = invertlinTree t (\x -> x)

revl l = revlist l (\x -> x)
revlist [] lc = lc []
revlist (x:xs) lc = revlist xs (\k -> x:(lc k))

-- revrun r = let (state, stack) = fromJust (toWhere r) in rev r (EndNur state stack)
--         where
--             rev (StartRun _ _) a = a
--             rev (PDAR r t) a = rev r (PDAN t a)

-- pda list functions (eg. just a regular list of transitions)
pdalcat :: (Eq st, Eq ind) => (st, [ind]) -> [PDATrans st sy ind] -> Maybe (st, [ind])
pdalcat cat [] = Just cat
-- pdalcat (q, []) (t:ts) = Nothing
pdalcat (q, stack) (t@(PDAT a _ c d e):ts) = let cl = length c in 
    if q == a && c == (take cl stack) then pdalcat (d, e++ (drop cl stack)) ts else Nothing

pdalyield [] = []
pdalyield (t@(PDAT _ b _ _ _):ts) = b : pdalyield ts

-- pdalshow :: (Eq st, Eq ind) => (st, [ind], [sy]) -> [PDATrans st sy ind] -> (st, [ind], [(PDATrans st sy ind, st, [ind], [sy])])
-- pdalshow (q, stack, yd) [] = (q, stack, [])
-- pdalshow (q, (i:is), yd) (t@(PDATrans a b c d e):ts) = (q, stack, (t, newq, newstack, yield ++ [b]) : list)
--     where
--         (q', s', list) = pdalshow recursion
--         cat = if q == a && i == c then Just (d, e++is) else Nothing

denoteplist :: ((PDATrans st sy ind) -> Term) -> [PDATrans st sy ind] -> Term
-- denoteplist mu [] = idterm
-- denoteplist mu (t:ts) = eval (funccomp # (mu t) # (denoteplist mu ts))
denoteplist mu ts = foldl' (\x -> \y -> eval (z ^ y # (x # z))) idterm (map mu ts)

denotep :: ((PDATrans st sy ind) -> Term) -> Term -> [PDATrans st sy ind] -> Term
-- denotep mu iota [] = iota
-- denotep mu iota (t:ts) = eval ()
denotep mu iota ts = foldl' (\x -> \y -> eval (Ap y x)) iota (map mu ts)

pdallog :: (Eq st, Eq ind) => (st, [ind]) -> [PDATrans st sy ind] -> [PDATrans st sy ind] -> [(PDATrans st sy ind, Maybe (st, [ind]), [sy])]
pdallog (q, stack) _ [] = []
pdallog (q, stack) taken (t:ts) = let updated = taken ++ [t] in 
    (t, pdalcat (q, stack) updated, pdalyield updated) : (pdallog (q, stack) updated ts)

-- ghci> pdallog (1,[Z]) [] pdal1

pdalshow (q, st, l) = pdallog (q, st) [] l

pdaltoTex lr@(q, st, l) = let log = pdalshow lr in
    let texit = \(t, cat, yd) -> "\\\\\n" ++ texify t ++ "  &  " ++ (case cat of {Just (q, st) -> showstate q ++ showstack st; Nothing -> "n/a"}) ++ "  &  " ++ concat yd in
        putStrLn ("\\begin{tabular}{lll}\n Start   &  " ++ showstate q ++ showstack st ++ "  &  " ++ concatMap texit log ++ "\n\\end{tabular}")

pdallogden mu iota (q, stack) _ [] = []
pdallogden mu iota (q, stack) taken (t:ts) = let updated = taken ++ [t] in 
    (t, pdalcat (q, stack) updated, pdalyield updated, denotep mu iota updated) : (pdallogden mu iota (q, stack) updated ts)

pdallogdentex lr@(q, st, l, mu, iota) = let log = pdallogden mu iota (q, st) [] l in
    let texit = \(t, cat, yd, den) -> "\\\\\n" ++ texify t ++ "  &  " ++ (case cat of {Just (q, st) -> showstate q ++ showstack st; Nothing -> "n/a"}) ++ "  &  " ++ concat yd ++ " & " ++ texify den in
        putStrLn ("\\begin{tabular}{lll}\n Start   &  " ++ showstate q ++ showstack st ++ "  &  " ++ " & " ++ texify iota ++ concatMap texit log ++ "\n\\end{tabular}")


------ OLD CODE FOR PDANUR

-- fromWhere :: (Eq st, Eq ind) => PDANur st sy ind -> Maybe (st, [ind])
-- fromWhere (EndNur s st) = Just (s, st)
-- fromWhere (PDAN t@(PDAT a _ c d e) rest) = case (fromWhere rest) of {Just (s, stack) -> if s == d then
--                     case addind c (strip e (Just stack)) of {Just newstack -> Just (a, newstack); Nothing -> Nothing} else Nothing;
--                     Nothing -> Nothing}
--     where
--         addind x Nothing = Nothing
--         addind x (Just xs) = Just (x:xs)
--         strip _ Nothing = Nothing
--         strip [] s = s
--         strip (x:xs) (Just (i:is)) = if x == i then strip xs (Just is) else Nothing

-- yieldpn (EndNur _ _) = []
-- yieldpn (PDAN (PDAT _ b _ _ _) rest) = b:(yieldpn rest)

-- pdantoAllTree (EndNur s st) = Node (show s ++ show st) []
-- pdantoAllTree r@(PDAN t rest) = Node ((show t) ++ '\n':cat ++ ": " ++ (concat (yieldpn r))) [pdantoAllTree rest]
--         where cat = case fromWhere r of {Just (cat,stack) -> show cat ++ show stack; Nothing -> "n/a"}




-- multipop PDA. for now, just duplicating the definitions of PDA to make MPDA, where popInd can be a list.
-- ultimately i should figure out how to combine this code...
data MPDATrans st sy ind = MPDAT {mfromState :: st, msymb :: sy, mpopInd :: [ind], mtoState :: st, mpushInd :: [ind]} deriving Eq

instance (Show st, Show sy, Show ind) => Show (MPDATrans st sy ind) where
    show (MPDAT a b c d e) = '(':show a ++ ',':show b ++ ',':show c ++ ") -> (" ++ show d ++ ',': show e ++")"

data MPDARun st sy ind = MEndRun st | MPDAR (MPDATrans st sy ind) (MPDARun st sy ind) deriving Eq

instance (Show st, Show sy, Show ind) => Show (MPDARun st sy ind) where
    show (MPDAR trans rest) = show trans ++ '\n':show rest

-- need to clean up all the maybes......
mfromWhere :: (Eq st, Eq ind) => MPDARun st sy ind -> Maybe (st, [ind])
mfromWhere (MEndRun s) = Just (s, [])
mfromWhere (MPDAR t@(MPDAT a _ c d e) rest) = case (mfromWhere rest) of {Just (s, stack) -> if s == d then
                    case addind c (strip e (Just stack)) of {Just newstack -> Just (a, newstack); Nothing -> Nothing} else Nothing;
                    Nothing -> Nothing}
    where
        addind x Nothing = Nothing
        addind x (Just xs) = Just (x ++ xs)
        strip _ Nothing = Nothing
        strip [] s = s
        strip (x:xs) (Just []) = Nothing
        strip (x:xs) (Just (i:is)) = if x == i then strip xs (Just is) else Nothing

yieldmp (MEndRun _) = []
yieldmp (MPDAR (MPDAT _ b _ _ _) rest) = b:(yieldmp rest)

mpdatoAllTree (MEndRun s) = Node (show s ++ "[]") []
mpdatoAllTree r@(MPDAR t rest) = Node ((show t) ++ '\n':cat ++ ": " ++ (concat (yieldmp r))) [mpdatoAllTree rest]
        where cat = case mfromWhere r of {Just (cat,stack) -> show cat ++ show stack; Nothing -> "n/a"}
