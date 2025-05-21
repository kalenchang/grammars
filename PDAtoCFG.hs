module PDAtoCFG where

import Prelude
import Data.Tree
import TreePrint
import PDA
import CFG

data PDAtransNT st sy ind = Sngp sy | Trpp st ind st deriving Eq

instance (Show st, Show sy, Show ind) => Show (PDAtransNT st sy ind) where
    show (Trpp a b c) = '[':show a ++ show b ++ show c ++ "]"
    show (Sngp a) = '[':show a ++ "]"

-- push/pop transitions -> becomes NT rule in CFG
-- need a list of intermediate states (sts) that will be used to pop the stack symbols added from this transition (e)
-- ideally sts and e are the same length
makeNTrule (PDAT a b c d e) sts = Branching (Trpp a c (last (d:sts))) ((Sngp b):(zipWith3 Trpp (d:sts) e sts))
-- rewrite Sngp nonterminals as terminals
makeTrule s = Leafing (Sngp s) [s]

-- makecfg' pdar = let (x,_) = makecfg pdar in x
makecfg :: PDARun st sy ind -> (CFTree (PDAtransNT st sy ind) sy, PDARun st sy ind)
makecfg (PDAR trans@(PDAT a b c d []) rest) = (CFT (makeNTrule (trans) []) [CFT (makeTrule b) []], rest)
makecfg (PDAR trans@(PDAT a b c d e) rest) = let (daughts, newrest, intersts) = makecfglist e rest in
                                            (CFT (makeNTrule trans intersts) ((CFT (makeTrule b) []):daughts), newrest)

-- maybe can add the S -> 1Z2 rule in this helper function?
makecfg' pdar start = let ((x:[]),_,_) = makecfglist [start] pdar in x
makecfglist :: [ind] -> PDARun st sy ind -> ([CFTree (PDAtransNT st sy ind) sy], PDARun st sy ind, [st])
makecfglist [] rest = ([], rest, []) -- (accum of CFTrees, remainder of PDA run, accumulation of denominators)
makecfglist (e1:es) (PDAR tr@(PDAT a b c d []) rests) = let (x,y,z) = makecfglist es rests in
                                    ((CFT (makeNTrule tr []) [CFT (makeTrule b) []]):x, y, d:z)
makecfglist (e1:es) (PDAR tr@(PDAT a b c d e) rests) = let (u,v,w) = (makecfglist e rests) in
                                    let (x,y,z) = makecfglist es v in
                                    ((CFT (makeNTrule tr w) ((CFT (makeTrule b) []):u)):x, y, (last w):z)
-- write an extractor function to get the denominator of the root node of a cfg tree

buildoutercfg pdar = let (x,_) = buildcfg pdar in x
-- assume we have a single state PDA for now. build the CFG tree
-- probably can treat buildcfg as a special case of buildlist, since buildlist is just a list of buildcfgs...
buildcfg :: PDARun st sy ind -> (CFTree ind sy, PDARun st sy ind)
buildcfg (PDAR trans@(PDAT a b c d []) rest) = (CFT (Leafing c [b]) [], rest)
buildcfg (PDAR trans@(PDAT a b c d e) rest) = let (daughts, newrest) = buildlist e rest in 
                                        (CFT (Branching c e) daughts, newrest)
    where
        buildlist [] rest = ([], rest)
        buildlist (e1:es) (PDAR tr rests) = let (z,w) = (buildlist (pushInd tr) rests) in
                                            let (x,y) = buildlist es w in
                                            ((CFT (Branching e1 (pushInd tr)) z):x, y)

-- > printTree $ cfgtoAllTree $ buildoutercfg pdar2