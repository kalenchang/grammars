module CFGtoPDA where

import Prelude
import Data.Tree
import TreePrint
import CFG
import PDA

------ top down PDA

tdpdaTrans :: Monoid ts => CFGRule nts ts -> PDATrans () ts nts 
tdpdaTrans (Branching a b) = PDAT () mempty [a] () b
tdpdaTrans (Leafing a [b]) = PDAT () b [a] () []

-- tdparse :: CFTree nts ts -> [PDATrans () ts nts]
-- tdparse (CFT r []) = [tdpdaTrans r]
-- tdparse (CFT r d) = (tdpdaTrans r) : concatMap tdparse d

-- listtorun :: [PDATrans () ts nts] -> PDARun () ts nts
-- listtorun [] = EndRun ()
-- listtorun (t:ts) = PDAR t (listtorun ts)

-- listtorun $ tdparse

-- OLD CODE FOR CONS LIST PDARUN
-- -- helper
-- tdparse' :: Monoid ts => [CFTree nts ts] -> PDARun () ts nts
-- tdparse' [] = EndRun ()
-- tdparse' ((CFT r d):rest) = PDAR (tdpdaTrans r) (tdparse' (d ++ rest))
-- -- actual
-- tdparse x = tdparse' [x]

-- -- new code for snoc list pdarun
-- tdparse :: Monoid ts => [CFTree VN ts] -> PDARun () ts VN
-- tdparse [] = StartRun () [CP]
-- tdparse ((CFT r d): rest) = undefined

cptlist :: Monoid ts => CFTree nts ts -> [PDATrans () ts nts]
cptlist (CFT (Leafing a [b]) []) = [PDAT () b [a] () []]
cptlist (CFT (Branching a b) ds) = (PDAT () mempty [a] () b) : (concatMap cptlist ds)


-- > printTree $ pdatoAllTree $ tdparse cfg2t1 

------ bottom up PDA

-- part of the problem is assuming that each PDA transition pops exactly 1 symbol. doesn't work for bottom up...
-- bupdaTrans :: Monoid ts => CFGRule nts ts -> PDATrans () ts nts 
-- bupdaTrans (Branching a b) = PDAT () 
-- bupdaTrans (Leafing a [b]) = PDAT () b []

data Addone t = Reg t | Addedone deriving Eq
instance Show t => Show (Addone t) where
    show Addedone = "Z"
    show (Reg t) = show t

bupdaTrans :: Monoid ts => CFGRule nts ts -> MPDATrans () ts (Addone nts) 
bupdaTrans (Branching a b) = MPDAT () mempty (reverse (map Reg b)) () [Reg a]
bupdaTrans (Leafing a [b]) = MPDAT () b [] () [Reg a]

-- helper function
buparse' :: Monoid ts => [CFTree nts ts] -> MPDARun () ts (Addone nts) -> MPDARun () ts (Addone nts)
buparse' [] run = run
buparse' ((CFT r d):rest) run = buparse' (d ++ rest) (MPDAR (bupdaTrans r) run)
-- actual bottom up parse
buparse x start = buparse' [x] (MPDAR (MPDAT () mempty [Reg start, Addedone] () []) (MEndRun ()))

cpblist :: Monoid ts => CFTree nts ts -> [PDATrans () ts (Addone nts)]
cpblist (CFT (Leafing a [b]) []) = [PDAT () b [] () [Reg a]]
cpblist (CFT (Branching a b) ds) = (concatMap cpblist ds) ++ [PDAT () mempty (map Reg (reverse b)) () [Reg a]]

cpbcomplete start d = cpblist d ++ [PDAT () mempty [Reg start, Addedone] () []]

-- a version of buparse using lists; requires listtorun
-- buparse :: Monoid ts => [CFTree nts ts] -> [MPDATrans () ts nts]
-- buparse (CFT r []) = [bupdaTrans r]
-- buparse (CFT r d) = (concatMap buparse d) ++ [bupdaTrans r]

-- > printTree $ mpdatoAllTree $ buparse cfg2t1 CP