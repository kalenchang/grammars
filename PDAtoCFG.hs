module PDAtoCFG where

import Prelude hiding ((^))
import Data.Tree

import Printing
import Lambdas
import PDA
import CFG

-- still need to add bar symbols...
data PDAtransNT st sy ind = PCStart | Sngp sy | Dblp st st | Trpp st ind st deriving Eq

instance (Show st, Show sy, Show ind) => Show (PDAtransNT st sy ind) where
    show (Trpp a b c) = '[':show a ++ show b ++ show c ++ "]"
    show (Dblp a b) = '[':show a ++ "-" ++ show b ++ "]"
    show (Sngp a) = '[':show a ++ "]"
    show PCStart = "S"

instance (Show st, Show ind) => Texable (PDAtransNT st String ind) where
    texify (Trpp a b c) = "\\tripcat{" ++ show a ++ "}{" ++ show c ++ "}{" ++ show b ++ "}"
    texify (Dblp a b) = "\\tripcat{" ++ show a ++ "}{" ++ show b ++ "}{}"
    texify (Sngp a) = if a == "" then "" else '!':texify a
    texify PCStart = "S"

-- these transitions are for pcg (greibach translation)
-- push/pop transitions -> becomes NT rule in CFG
-- need a list of intermediate states (sts) that will be used to pop the stack symbols added from this transition (e)
-- in theory sts and e are the same length
makeNTrule (PDAT q u [i] q' js) sts = Branching (Trpp q i (last (q':sts))) ((Sngp u):(zipWith3 Trpp (q':sts) js sts))
-- rewrite Sngp nonterminals as terminals
makeTrule s = Leafing (Sngp s) [s]
-- if stack is empty, can rewrite NT as T
makeNTTrule (PDAT q u [i] q' []) = Leafing (Trpp q i q') [u]


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

-- pcg is pda to cfg via "greibach" translation
-- pcg requires a starting stack symbol
pcg :: (PDARun st sy ind) -> (CFTree (PDAtransNT st sy ind) sy)
pcg (p, state, index) = let (t, s) = head $ pcgm p in
    (CFT (Branching PCStart [Trpp state index s]) [t])

-- pcgm is the recursive component of pcg
-- [c] ensures that each transition pops exactly one index, and errors otherwise
pcgm :: [PDATrans st sy ind] -> [(CFTree (PDAtransNT st sy ind) sy, st)]
pcgm [] = []
pcgm (tr@(PDAT q u [i] q' []):ts) = (CFT (makeNTTrule tr) [], q'):(pcgm ts)
pcgm (tr@(PDAT q u [i] q' js):ts) = let (treelist, rank) = (pcgm ts, length js) in
    let (lf, lb) = (take rank treelist, drop rank treelist) in
    (CFT (makeNTrule tr (map snd lf)) ((CFT (makeTrule u) []):(map fst lf)), snd $ last lf):lb

-- todo: still need to add semantic translations, also do examples to check

-------------------
makepcmrule tr@(PDAT q u [] q' []) x 
    | u == mempty = Branching (Dblp q x) [Dblp q' x]
    | otherwise = Branching (Dblp q x) [Sngp u, Dblp q' x]
makepcmrule tr@(PDAT q u [] q' [j]) x 
    | u == mempty = Branching (Dblp q x) [Trpp q' j x]
    | otherwise = Branching (Dblp q x) [Sngp u, Trpp q' j x]
makepcmrule tr@(PDAT s u [i] s' []) x 
    | u == mempty = Branching (Trpp s i x) [Dblp s' x]
    | otherwise = Branching (Trpp s i x) [Sngp u, Dblp s' x]
makepcmcompose q s x i = Branching (Trpp q i x) [Dblp q s, Trpp s i x]
makepcmlextree u = if null u then [] else [CFT (Leafing (Sngp u) [u]) []]
makepcmstart x = Branching PCStart [x]

-- pcm is the pda to cfg "sipser" translation
-- pcm' is the recursive part of pcm that accepts the denominator ('hole') as a second argument
-- pcm' :: (Eq st, Eq ind) => [PDATrans st sy ind] -> (PDAtransNT st sy ind) -> CFTree (PDAtransNT st sy ind) sy
pcm' [] c@(Dblp s s') | s == s' = CFT (Leafing c []) []
pcm' (tr@(PDAT q u [] q' []):ts) c@(Dblp w x) | q == w = CFT (makepcmrule tr x) ((makepcmlextree u) ++ [pcm' ts (Dblp q' x)])
pcm' (tr@(PDAT q u [] q' [j]):ts) c@(Dblp w x) | q == w = CFT (makepcmrule tr x) ((makepcmlextree u) ++ [pcm' ts (Trpp q' j x)])
pcm' (tr@(PDAT q u [i] q' []):ts) c@(Trpp w k x) | q == w && i == k = CFT (makepcmrule tr x) ((makepcmlextree u) ++ [pcm' ts (Dblp q' x)])
pcm' p@(tr@(PDAT q u [] q' _):ts) c@(Trpp w k x) | q == w = let (lf, pop@(PDAT s v [i] s' []), lb) = splitpath [k] p in -- splitpath ensures k == i
                CFT (makepcmcompose q s x i) [pcm' lf (Dblp q s), pcm' (pop:lb) (Trpp s i x)]

splitpath :: Eq ind => [ind] -> [PDATrans st sy ind] -> ([PDATrans st sy ind], PDATrans st sy ind, [PDATrans st sy ind])
-- splitpath [] (t:ts) = ([], t, ts)
splitpath inds (t@(PDAT _ _ [] _ []):ts) = let (f, m, b) = splitpath inds ts in (t:f, m, b)
splitpath inds (t@(PDAT _ _ [] _ [pushi]):ts) = let (f, m, b) = splitpath (pushi:inds) ts in (t:f, m, b)
splitpath (i:is) (t@(PDAT _ _ [popi] _ []):ts)
    | (popi == i) = if (null is) then ([], t, ts) else let (f, m, b) = splitpath is ts in (t:f, m, b)

-- all PDAs now start with single stack symbol
-- pcm :: (Eq st, Eq ind) => (PDARun st sy ind) -> CFTree (PDAtransNT st sy ind) sy
pcm r@(p, s, i) = let Just (d, []) = pdarcat r in 
    let startcat = (Trpp s i d) in 
        CFT (makepcmstart startcat) [pcm' p startcat]

-- > latexTree $ cfgtoThreeLatex $ pcm pda3r1

-- pcmmu will output a list of rules for a single transition. need to feed it a list of all possible cats
pcmmu cats (trans, int) = [ (makepcmrule trans s, newint) | s <- cats]
    where newint = if (symb trans == mempty)
                    then k ^ x ^ k # (int # x)
                    else g ^ k ^ x ^ k # (int # x)

makemupcm (PDA sts syms inds _ q0 z0) mulist iota = (concatMap (pcmmu sts) mulist)  -- transition rules
                                        ++ [(makepcmcompose q s s' i, x ^ y ^ z ^ y # (x # z)) | q <- sts, s <- sts, s' <- sts, i <- inds] -- compose rules
                                        ++ [(Leafing (Dblp s s) [], idterm) | s <- sts]  -- empty rules
                                        ++ [(Leafing (Sngp u) [u], idterm) | u <- syms]  -- lexical rules
                                        ++ [(Branching PCStart [(Trpp q0 z0 s)], k ^ k # iota) | s <- sts]  -- start rules

pcmpda3mu = lookupint $ makemupcm pda3 mupda3list iotapda3
-- > latexTree $ cfgtoAllLatex pcmpda3mu (pcm pda3r1)
