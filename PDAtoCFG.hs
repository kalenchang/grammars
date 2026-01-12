module PDAtoCFG where

import Prelude hiding ((^))
import Data.Tree

import Printing
import Lambdas
import PDA
import CFG

-- still need to add bar symbols...
data PDAtransNT st sy ind = PCStart | Sngp sy | Dblp st st Bool | Trpp st ind st Bool deriving Eq

instance (Show st, Show sy, Show ind) => Show (PDAtransNT st sy ind) where
    show (Trpp a b c d) = '[':show a ++ show b ++ show c ++ "]"
    show (Dblp a c d) = '[':show a ++ "-" ++ show c ++ (if d then "." else "") ++ "]"
    show (Sngp a) = '[':show a ++ "]"
    show PCStart = "S"

instance (Show st, Show ind) => Texable (PDAtransNT st String ind) where
    texify (Trpp a b c d) = "\\tripcat{" ++ show a ++ "}{" ++ (if d then \x -> "\\xbar{" ++ x ++ "}" else id) (show c) ++ "}{" ++ show b ++ "}"
    texify (Dblp a c d) = "\\tripcat{" ++ show a ++ "}{" ++ (if d then \x -> "\\xbar{" ++ x ++ "}" else id) (show c) ++ "}{}"
    texify (Sngp a) = if a == "" then "" else "\\inbar{" ++ texify a ++ "}"
    texify PCStart = "S"

-- PCT section

-- these transitions are for pct (greibach translation)
-- push/pop transitions -> becomes NT rule in CFG
-- need a list of intermediate states (sts) that will be used to pop the stack symbols added from this transition (e)
-- in theory sts and e are the same length
makeNTrule (PDAT q u [i] q' js) sts = Branching (Trpp q i (last (q':sts)) False) ((Sngp u):(zipWith3 (\x -> \y -> \z -> Trpp x y z False) (q':sts) js sts ))
-- rewrite Sngp nonterminals as terminals
makeTrule s = Leafing (Sngp s) [s]
-- if stack is empty, can rewrite NT as T
makeNTTrule (PDAT q u [i] q' []) = Leafing (Trpp q i q' False) [u]


-- -- write an extractor function to get the denominator of the root node of a cfg tree
-- makecfg' pdar start = let ((x:[]),_,_) = makecfglist [start] pdar in x
-- makecfglist :: [ind] -> [PDATrans st sy ind] -> ([CFTree (PDAtransNT st sy ind) sy], [PDATrans st sy ind], [st])
-- makecfglist [] ts = ([], ts, []) -- (accum of CFTrees, remainder of PDA run, accumulation of denominators)
-- makecfglist (e1:es) (tr@(PDAT a b c d []):rests) = let (x,y,z) = makecfglist es rests in
--                                     ((CFT (makeNTrule tr []) [CFT (makeTrule b) []]):x, y, d:z)
-- makecfglist (e1:es) (tr@(PDAT a b c d e):rests) = let (u,v,w) = (makecfglist e rests) in
--                                     let (x,y,z) = makecfglist es v in
--                                     ((CFT (makeNTrule tr w) ((CFT (makeTrule b) []):u)):x, y, (last w):z)


----------------
-- -- OLD PCT, where pct' has type P(A) -> [D(G) x Q]
-- -- pct is pda to cfg via top down "ungreibach" translation
-- -- pct requires a starting stack symbol
-- pct :: (PDARun st sy ind) -> (CFTree (PDAtransNT st sy ind) sy)
-- pct (p, state, index) = let (t, s) = head $ pct' p in
--     (CFT (Branching PCStart [Trpp state index s False]) [t])

-- -- pct' is the recursive component of pct
-- -- [c] ensures that each transition pops exactly one index, and errors otherwise
-- pct' :: [PDATrans st sy ind] -> [(CFTree (PDAtransNT st sy ind) sy, st)]
-- pct' [] = []
-- pct' (tr@(PDAT q u [i] q' []):ts) = (CFT (makeNTTrule tr) [], q'):(pct' ts)
-- pct' (tr@(PDAT q u [i] q' js):ts) = let (treelist, rank) = (pct' ts, length js) in
--     let (lf, lb) = (take rank treelist, drop rank treelist) in
--     (CFT (makeNTrule tr (map snd lf)) ((CFT (makeTrule u) []):(map fst lf)), snd $ last lf):lb

-- todo: still need to add semantic translations, also do examples to check

-- NEW PCT: pct' has type P(A) -> [D(G)]
-- pct is pda to cfg via top down "ungreibach" translation
-- pct requires a starting stack symbol
pct :: (Eq st, Eq ind) => (PDARun st sy ind) -> (CFTree (PDAtransNT st sy ind) sy)
pct (p, state, index) = (CFT (Branching PCStart [Trpp state index x False]) [head $ pct' p])
    where Just (x, []) = pdarcat (p, state, index)

-- pct' is the recursive component of pct
-- [i] ensures that each transition pops exactly one index, and errors otherwise
pct' :: [PDATrans st sy ind] -> [CFTree (PDAtransNT st sy ind) sy]
pct' [] = []
pct' (tr@(PDAT q u [i] q' []):ts) = (CFT (makeNTTrule tr) []):(pct' ts)
pct' (tr@(PDAT q u [i] q' js):ts) = let (treelist, rank) = (pct' ts, length js) in
    let (lf, lb) = (take rank treelist, drop rank treelist) in
    (CFT (makeNTrule tr (map rtdn lf)) ((CFT (makeTrule u) []):lf)):lb

-- root denominator
rtdn (CFT (Branching (Trpp _ _ x _) _) _) = x
rtdn (CFT (Leafing (Trpp _ _ x _) _) _) = x

-- create mu' for the new cfg
pctmu sts (trans, int)
    | pushInd trans == [] = [ (makeNTTrule trans, int) ]
    | otherwise = let rank = length $ pushInd trans in
        [ (makeNTrule trans stlist, (pctterm rank) # int) | stlist <- powerlist rank sts ]

powerlist 0 bank = [[]]
powerlist n bank = [ x:rest | x <- bank, rest <- powerlist (n-1) bank]

makemupct (PDA sts syms inds _ q0 z0) mulist iota = (concatMap (pctmu sts) mulist)  -- transition rules
                                        ++ [(Leafing (Sngp u) [u], idterm) | u <- syms]  -- lexical rules
                                        ++ [(Branching PCStart [(Trpp q0 z0 s False)], k ^ k # iota) | s <- sts]  -- start rules

pctpda4mu = lookupint $ makemupct pda4 mupda4list iotapda4

-- > pdartoTex pda4r1
-- > latexTree $ cfgtoThreeLatex $ pct pda4r1

-- > pdallogdentex pda4r1 mupda4 iotapda4
-- 

{-
TODO: make a type for "rule schemas" so that mus can just store these schemas, rather than
instantiating each rule. that would mean some kind of data type which looks like a cfg rule,
but stores as much data as a pda transition. so for [1X3] -> [u] [1Y2] [2Z3], it would only 
match the 1, 3, u, X, and YZ (everything in a pda transition)

OR: maybe this is a good idea(?): instead of state type st, do state type st + 1, 
such that the 1 can match with anything ie. when checking if a (PDAtransNT st sy ind) 
matches a (PDAtransNT (st + 1) sy ind), just return true if st + 1 is 1. ("wildcard"/variable).
do we need to ensure the variables line up? eg. in valid CFG rules: x/y y/z, you won't have x/y z/y.
perhaps we can just assume that any rule being looked up in mu is well-formed.
the only downside is that when printing, eg. interpretation tables, you cant show diff wildcards.
but checking variable bindings would be annoying. compromise: all states match any variable in
the lookup table, but they are stored as diff variables so that they can be printed differently
-}

-------------------
-- PCM SECTION: pda to cfg, max one

makepcmrule tr@(PDAT q u [] q' []) x bar
    | u == mempty = Branching (Dblp q x bar) [Dblp q' x False]
    | otherwise = Branching (Dblp q x bar) [Sngp u, Dblp q' x False]
makepcmrule tr@(PDAT q u [] q' [j]) x bar
    | u == mempty = Branching (Dblp q x bar) [Trpp q' j x False]
    | otherwise = Branching (Dblp q x bar) [Sngp u, Trpp q' j x False]
makepcmrule tr@(PDAT s u [i] s' []) x bar
    | u == mempty = Branching (Trpp s i x bar) [Dblp s' x False]
    | otherwise = Branching (Trpp s i x bar) [Sngp u, Dblp s' x False]
makepcmcompose q s x i = Branching (Trpp q i x False) [Dblp q s True, Trpp s i x True]
makepcmlextree u = if null u then [] else [CFT (Leafing (Sngp u) [u]) []]
makepcmstart x = Branching PCStart [x]

-- pcm is the pda to cfg "sipser" translation
-- pcm' is the recursive part of pcm that accepts the denominator ('hole') as a second argument
-- pcm' :: (Eq st, Eq ind) => [PDATrans st sy ind] -> (PDAtransNT st sy ind) -> CFTree (PDAtransNT st sy ind) sy
pcm' [] c@(Dblp s s' False) | s == s' = CFT (Leafing c []) []
pcm' (tr@(PDAT q u [] q' []):ts) c@(Dblp w x bar) | q == w = CFT (makepcmrule tr x bar) ((makepcmlextree u) ++ [pcm' ts (Dblp q' x False)])
pcm' (tr@(PDAT q u [] q' [j]):ts) c@(Dblp w x bar) | q == w = CFT (makepcmrule tr x bar) ((makepcmlextree u) ++ [pcm' ts (Trpp q' j x False)])
pcm' (tr@(PDAT q u [i] q' []):ts) c@(Trpp w k x bar) | q == w && i == k = CFT (makepcmrule tr x bar) ((makepcmlextree u) ++ [pcm' ts (Dblp q' x False)])
pcm' p@(tr@(PDAT q u [] q' _):ts) c@(Trpp w k x False) | q == w = let (lf, pop@(PDAT s v [i] s' []), lb) = splitpath [k] p in -- splitpath ensures k == i
                CFT (makepcmcompose q s x i) [pcm' lf (Dblp q s True), pcm' (pop:lb) (Trpp s i x True)]

splitpath :: Eq ind => [ind] -> [PDATrans st sy ind] -> ([PDATrans st sy ind], PDATrans st sy ind, [PDATrans st sy ind])
-- splitpath [] (t:ts) = ([], t, ts)
splitpath inds (t@(PDAT _ _ [] _ []):ts) = let (f, m, b) = splitpath inds ts in (t:f, m, b)
splitpath inds (t@(PDAT _ _ [] _ [pushi]):ts) = let (f, m, b) = splitpath (pushi:inds) ts in (t:f, m, b)
splitpath (i:is) (t@(PDAT _ _ [popi] _ []):ts)
    | (popi == i) = if (null is) then ([], t, ts) else let (f, m, b) = splitpath is ts in (t:f, m, b)

-- all PDAs now start with single stack symbol
-- pcm :: (Eq st, Eq ind) => (PDARun st sy ind) -> CFTree (PDAtransNT st sy ind) sy
pcm r@(p, s, i) = let Just (d, []) = pdarcat r in 
    let startcat = (Trpp s i d False) in 
        CFT (makepcmstart startcat) [pcm' p startcat]

-- > latexTree $ cfgtoThreeLatex $ pcm pda3r1

-- pcmmu will output a list of rules for a single transition. need to feed it a list of all possible cats
pcmmu sts (trans, int) = [ (makepcmrule trans s bar, newint) | s <- sts, bar <- [True, False]]
    where newint = if (symb trans == mempty)
                    then k ^ x ^ k # (int # x)
                    else g ^ k ^ x ^ k # (int # x)

makemupcm (PDA sts syms inds _ q0 z0) mulist iota = (concatMap (pcmmu sts) mulist)  -- transition rules
                                        ++ [(makepcmcompose q s s' i, x ^ y ^ z ^ y # (x # z)) | q <- sts, s <- sts, s' <- sts, i <- inds] -- compose rules
                                        ++ [(Leafing (Dblp s s False) [], idterm) | s <- sts]  -- empty rules
                                        ++ [(Leafing (Sngp u) [u], idterm) | u <- syms]  -- lexical rules
                                        ++ [(Branching PCStart [(Trpp q0 z0 s False)], k ^ k # iota) | s <- sts]  -- start rules

pcmpda3mu = lookupint $ makemupcm pda3 mupda3list iotapda3
-- > latexTree $ cfgtoAllLatex pcmpda3mu (pcm pda3r1)

-- pcmgram (PDA sts syms inds trs q0 z0) = [makepcmrule tr s | s <- sts, tr <- trs]
