module CFGtoPDA where

import Prelude hiding ((^))
import Data.Tree

import Printing
import Lambdas
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
cptlist (CFT r@(Leafing a [b]) []) = [tdpdaTrans r]
cptlist (CFT r@(Branching a b) ds) = (tdpdaTrans r) : (concatMap cptlist ds)

cpt1l1 = cptlist cfg1t1 

-- > pdalshow ((),[CP],cpt1l1)

-- code to transform mus
cptmu :: Monoid ts => (CFGRule nts ts, Term) -> (PDATrans () ts nts, Term)
cptmu (rule, int) = (tdpdaTrans rule, eval (holdout (rankc rule) # int))
iotacpt = idterm

mucpt1 = lookupint (map cptmu mucfg1list)

-- ghci> denotec mucfg1 cfg1t1 
-- let' (run' john') mary'

-- > denotep mucpt1 iotacpt cpt1l1


------ bottom up PDA

-- part of the problem is assuming that each PDA transition pops exactly 1 symbol. doesn't work for bottom up...
-- bupdaTrans :: Monoid ts => CFGRule nts ts -> PDATrans () ts nts 
-- bupdaTrans (Branching a b) = PDAT () 
-- bupdaTrans (Leafing a [b]) = PDAT () b []

data Addone t = Reg t | Addedone deriving Eq
instance Show t => Show (Addone t) where
    show Addedone = "Z"
    show (Reg t) = show t

bupdaTrans :: Monoid ts => CFGRule nts ts -> PDATrans () ts (Addone nts) 
bupdaTrans (Branching a b) = PDAT () mempty (reverse (map Reg b)) () [Reg a]
bupdaTrans (Leafing a [b]) = PDAT () b [] () [Reg a]

-- -- helper function
-- buparse' :: Monoid ts => [CFTree nts ts] -> PDARun () ts (Addone nts) -> PDARun () ts (Addone nts)
-- buparse' [] run = run
-- buparse' ((CFT r d):rest) run = buparse' (d ++ rest) (PDAR (bupdaTrans r) run)
-- -- actual bottom up parse
-- buparse x start = buparse' [x] (PDAR (PDAT () mempty [Reg start, Addedone] () []) (EndRun ()))

cpblist :: Monoid ts => CFTree nts ts -> [PDATrans () ts (Addone nts)]
cpblist (CFT (Leafing a [b]) []) = [PDAT () b [] () [Reg a]]
cpblist (CFT (Branching a b) ds) = (concatMap cpblist ds) ++ [PDAT () mempty (map Reg (reverse b)) () [Reg a]]

cpbcomplete start d = cpblist d ++ [PDAT () mempty [Reg start, Addedone] () []]

-- a version of buparse using lists; requires listtorun
-- buparse :: Monoid ts => [CFTree nts ts] -> [MPDATrans () ts nts]
-- buparse (CFT r []) = [bupdaTrans r]
-- buparse (CFT r d) = (concatMap buparse d) ++ [bupdaTrans r]

-- > printTree $ mpdatoAllTree $ buparse cfg2t1 CP

cpbmu (rule, int) = let rk = rankc rule in (bupdaTrans rule, eval (bcomb # ((holdout rk) # (revlam rk int))))
iotacpb = idterm

makemucpb startsym mulist = lookupint (map cpbmu mulist ++ [(PDAT () mempty [Reg startsym, Addedone] () [], lowerid)])

mucpbl1 = makemucpb CP mucfg1list

-- > pdaltoTex ((), [Addedone], cpbcomplete CP cfg1t1)
-- > pdallogdentex ((), [Addedone], cpbcomplete CP cfg1t1, mucpbl1, iotacpb)