module PDA where

import Prelude
import TreePrint
import Data.Tree

data Stacksymb = Y | Z deriving (Eq, Show)

-- top of stack is left (outermost element on list)
data PDATrans st sy ind = PDAT {fromState :: st, symb :: sy, popInd :: ind, toState :: st, pushInd :: [ind]} deriving Eq
-- I think I want to keep symb as [sy] so that I have a 0 element for general sy, not just strings?
-- or make it monoidal?

instance (Show st, Show sy, Show ind) => Show (PDATrans st sy ind) where
    show (PDAT a b c d e) = '(':show a ++ ',':show b ++ ',':show c ++ ") -> (" ++ show d ++ ',': show e ++")"

data PDARun st sy ind = EndRun st | PDAR (PDATrans st sy ind) (PDARun st sy ind) deriving Eq

instance (Show st, Show sy, Show ind) => Show (PDARun st sy ind) where
    show (PDAR trans rest) = show trans ++ '\n':show rest

pdat1 = PDAT 1 "NP " Z 1 [Z, Z]
pdat2 = PDAT 1 "" Z 2 []
pdat3 = PDAT 2 "V " Z 2 []

pdar1 = PDAR pdat1 (
            PDAR pdat1 (
                PDAR pdat2 (
                    PDAR pdat3 (
                        PDAR pdat3 (EndRun 2)
                    )
                )
            )
        )

pdar2 = PDAR pdat1 (
            PDAR pdat1 (
                PDAR pdat1 (
                    PDAR pdat2 (
                        PDAR pdat3 (
                            PDAR pdat3 (
                                PDAR pdat3 (EndRun 2)
                            )
                        )
                    )
                )
            )
        )

pdat11 = PDAT 1 "NP " Z 1 [Z, Y]
pdat12 = PDAT 1 "" Z 1 []
pdat13 = PDAT 1 "V " Y 1 []

pdar11 = PDAR pdat11 (
            PDAR pdat11 (
                PDAR pdat12 (
                    PDAR pdat13 (
                        PDAR pdat13 (EndRun 1)
                    )
                )
            )
        )

-- need to clean up all the maybes......
fromWhere :: (Eq st, Eq ind) => PDARun st sy ind -> Maybe (st, [ind])
fromWhere (EndRun s) = Just (s, [])
fromWhere (PDAR t@(PDAT a _ c d e) rest) = case (fromWhere rest) of {Just (s, stack) -> if s == d then
                    case addind c (strip e (Just stack)) of {Just newstack -> Just (a, newstack); Nothing -> Nothing} else Nothing;
                    Nothing -> Nothing}
    where
        addind x Nothing = Nothing
        addind x (Just xs) = Just (x:xs)
        strip _ Nothing = Nothing
        strip [] s = s
        strip (x:xs) (Just (i:is)) = if x == i then strip xs (Just is) else Nothing

yieldp (EndRun _) = []
yieldp (PDAR (PDAT _ b _ _ _) rest) = b:(yieldp rest)

pdatoAllTree (EndRun s) = Node (show s ++ "[]") []
pdatoAllTree r@(PDAR t rest) = Node ((show t) ++ '\n':cat ++ ": " ++ (concat (yieldp r))) [pdatoAllTree rest]
        where cat = case fromWhere r of {Just (cat,stack) -> show cat ++ show stack; Nothing -> "n/a"}




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
