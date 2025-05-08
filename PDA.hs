module PDA where

import Prelude
import TreePrint
import Data.Tree

data Stacksymb = Y | Z deriving (Eq, Show)

-- top of stack is left (outermost element on list)
data PDATrans st sy ind = PDAT {fromState :: st, symb :: sy, popInd :: ind, toState :: st, pushInd :: [ind]} deriving Eq

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

