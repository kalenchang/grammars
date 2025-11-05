module PDAtoCFG where

import Prelude
import Data.Tree

import Printing
import PDA
import CFG

data PDAtransNT st sy ind = PCStart | Sngp sy | Dblp st st | Trpp st ind st deriving Eq

instance (Show st, Show sy, Show ind) => Show (PDAtransNT st sy ind) where
    show (Trpp a b c) = '[':show a ++ show b ++ show c ++ "]"
    show (Dblp a b) = '[':show a ++ "-" ++ show b ++ "]"
    show (Sngp a) = '[':show a ++ "]"
    show PCStart = "S"

instance (Show st, Texable sy, Show ind) => Texable (PDAtransNT st sy ind) where
    texify (Trpp a b c) = "\\tripcat{" ++ show a ++ "}{" ++ show c ++ "}{" ++ show b ++ "}"
    texify (Dblp a b) = "\\tripcat{" ++ show a ++ "}{" ++ show b ++ "}{}"
    texify (Sngp a) = '!':texify a
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
-- pcg requires a starting stack symbol, so Just index
pcg :: (PDARun st sy ind) -> (CFTree (PDAtransNT st sy ind) sy)
pcg (p, state, Just index) = let (t, s) = head $ pcgm p in
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
makepcsrule tr@(PDAT q u [] q' []) x = Branching (Dblp q x) [Sngp u, Dblp q' x]
makepcsrule tr@(PDAT q u [] q' [j]) x = Branching (Dblp q x) [Sngp u, Trpp q' j x]
makepcsrule tr@(PDAT s v [i] s' []) x = Branching (Trpp s i x) [Sngp v, Dblp s' x]
makepcscompose q s x i = Branching (Trpp q i x) [Dblp q s, Trpp s i x]
makepcslex u = Leafing (Sngp u) [u]
makepcsstart s d = Branching PCStart [Dblp s d]

-- pcs is the pda to cfg "sipser" translation
-- pcsh is the recursive part of pcs that accepts the denominator ('hole') as a second argument
pcsh :: Eq ind => [PDATrans st sy ind] -> st -> CFTree (PDAtransNT st sy ind) sy
pcsh [] s = CFT (Leafing (Dblp s s) []) []
pcsh (tr@(PDAT q u [] q' []):ts) x = CFT (makepcsrule tr x) [CFT (makepcslex u) [], pcsh ts x]
pcsh (tr@(PDAT q u [] q' [j]):ts) x = let (lf, pop@(PDAT s v [i] s' []), lb) = splitpath [j] ts in
    if null lf
        then CFT (makepcsrule tr x) [
                CFT (makepcslex u) [], 
                CFT (makepcsrule pop x) [
                    CFT (makepcslex v) [],
                    pcsh lb x
                ]
            ]
        else CFT (makepcsrule tr x) [
                CFT (makepcslex u) [], 
                CFT (makepcscompose q' s x i) [ -- j should equal i if the code is right, so can use either j or i here
                    pcsh lf s,
                    CFT (makepcsrule pop x) [
                        CFT (makepcslex v) [],
                        pcsh lb x
                    ]
                ] 
            ]

splitpath :: Eq ind => [ind] -> [PDATrans st sy ind] -> ([PDATrans st sy ind], PDATrans st sy ind, [PDATrans st sy ind])
-- splitpath [] (t:ts) = ([], t, ts)
splitpath inds (t@(PDAT _ _ [] _ []):ts) = let (f, m, b) = splitpath inds ts in (t:f, m, b)
splitpath inds (t@(PDAT _ _ [] _ [pushi]):ts) = let (f, m, b) = splitpath (pushi:inds) ts in (t:f, m, b)
splitpath (i:is) (t@(PDAT _ _ [popi] _ []):ts)
    | (popi == i) = if (null is) then ([], t, ts) else let (f, m, b) = splitpath is ts in (t:f, m, b)

-- currently, pcs requires starting from an empty stack, so the starting stack symbol should be Nothing
pcs :: (Eq st, Eq ind) => (PDARun st sy ind) -> CFTree (PDAtransNT st sy ind) sy
pcs r@(p, s, Nothing) = let Just (d, []) = pdarcat r in CFT (makepcsstart) [pcsh p d]

pcsmu (trans, int) = undefined


-- cpbmu (rule, int) = let rk = rankc rule in (bupdaTrans rule, eval (bcomb # ((holdout rk) # (revlam rk int))))
-- iotacpb = idterm

-- makemucpb startsym mulist = lookupint (map cpbmu mulist ++ [(PDAT () mempty [Reg startsym, Addedone] () [], lowerid)])

-- mucpbl1 = makemucpb CP mucfg1list