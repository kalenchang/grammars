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
showstack s = "[" ++ insertSpaces s ++ "]"

type PDARun st sy ind = ([PDATrans st sy ind], st, ind)

data PDA st sy ind = PDA {q :: [st], sigma :: [sy], gamma :: [ind], delta :: [PDATrans st sy ind], q0 :: st, z0 :: ind}

-- pda1: an bn
pdat1 = PDAT 1 "a" [Z] 1 [Z, Z]
pdat2 = PDAT 1 "" [Z] 2 []
pdat3 = PDAT 2 "b" [Z] 2 []

-- a3b3
pdal1 = [pdat1, pdat1, pdat1, pdat2, pdat3, pdat3, pdat3]
pdar1 = (pdal1, 1, Z)

-- pda2: center embedding
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

-- pda3: wwR
pda3t1 = PDAT 1 "a" [] 1 [A]
pda3t2 = PDAT 1 "b" [] 1 [B]
pda3t3 = PDAT 1 "" [] 2 []
pda3t4 = PDAT 2 "a" [A] 2 []
pda3t5 = PDAT 2 "b" [B] 2 []
pda3t6 = PDAT 2 "" [C] 2 []

pda3 = PDA [1,2] ["a","b"] [A,B,C] [pda3t1,pda3t2,pda3t3,pda3t4,pda3t5,pda3t6] 1 C

pda3l1 = [pda3t1, pda3t1, pda3t2, pda3t3, pda3t5, pda3t4, pda3t4, pda3t6]
pda3r1 = (pda3l1, 1, C)

mupda3list = [
    (pda3t1, up'),
    (pda3t2, flr'),
    (pda3t3, idterm),
    (pda3t4, up'),
    (pda3t5, flr'),
    (pda3t6, idterm)]
mupda3 = lookupint mupda3list
iotapda3 = no'

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

-- invertlinTree :: Tree a -> ([Tree a] -> [Tree a]) -> Tree a
-- invertlinTree (Node n []) tc = (Node n (tc []))
-- invertlinTree (Node n (x:xs)) tc = invertlinTree x (\k -> [Node n (tc k)])
-- invlin t = invertlinTree t (\x -> x)

revl l = revlist l (\x -> x)
revlist [] lc = lc []
revlist (x:xs) lc = revlist xs (\k -> x:(lc k))

-- pda list functions (eg. just a regular list of transitions)
-- pdalcat :: (Eq st, Eq ind) => (st, [ind]) -> [PDATrans st sy ind] -> Maybe (st, [ind])
pdalcat cat [] = Just cat
-- pdalcat (q, []) (t:ts) = Nothing
pdalcat (q, stack) (t@(PDAT a _ c d e):ts) = let cl = length c in 
    if q == a && c == (take cl stack) then pdalcat (d, e++ (drop cl stack)) ts else Nothing
pdarcat (translist, startstate, startindex) = pdalcat (startstate, [startindex]) translist
-- pdarcat (translist, startstate, Nothing) = pdalcat (startstate, []) translist

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

-- pdarshow :: (Eq st, Eq ind) => ([PDATrans st sy ind], st, ind) -> [(PDATrans st sy ind, Maybe (st, [ind]), [sy])]
pdarshow (l, q, st) = pdallog (q, [st]) [] l

pdartoTex run@(l, q, st) = let log = pdarshow run in
    let texit = \(t, cat, yd) -> "\\\\\n" ++ texify t ++ "  &  " ++ (case cat of {Just (q, st) -> showstate q ++ showstack st; Nothing -> "n/a"}) ++ "  &  " ++ concat yd in
        putStrLn ("\n\\begin{tabular}{lll}\n Start   &  " ++ showstate q ++ showstack [st] ++ "  &  " ++ concatMap texit log ++ "\n\\end{tabular}\n")

pdallogden mu iota (q, stack) _ [] = []
pdallogden mu iota (q, stack) taken (t:ts) = let updated = taken ++ [t] in 
    (t, pdalcat (q, stack) updated, pdalyield updated, denotep mu iota updated) : (pdallogden mu iota (q, stack) updated ts)

-- pdallogdentex :: (Eq st, Eq ind, Show st, Show ind) => ([PDATrans st sy ind], st, [ind]) -> (PDATrans st sy ind -> Term) -> Term -> IO ()
pdallogdentex run@(l, q, i) mu iota = let log = pdallogden mu iota (q, [i]) [] l in
    let texit = \(t, cat, yd, den) -> "\\\\\n" ++ texify t ++ "  &  " ++ (case cat of {Just (q, stack) -> showstate q ++ showstack stack; Nothing -> "n/a"}) ++ "  &  " ++ concat yd ++ " & " ++ texify den in
        putStrLn ("\n\n\\begin{tabular}{llll}\n Start   &  " ++ showstate q ++ showstack [i] ++ "  &  " ++ " & " ++ texify iota ++ concatMap texit log ++ "\n\\end{tabular}\n\n")

pdatoTex (PDA q sigma gamma delta q0 z0) = putStrLn $ "\n$(" ++ concatMap bracketize [show q, show sigma, show gamma] ++ "\\delta, " 
                                                ++ show q0 ++ ", " ++ show z0 ++ ")$, where $\\delta = \\{" ++ concatMap (\x -> "\\hlm{" ++ texify x ++ "},") delta ++ "\\}$\n"
bracketize s = "\\{" ++ s ++ "\\}, "