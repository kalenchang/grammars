module Printing where

import Prelude
import Data.Tree

-- rule showing functions
insertSpaces :: Show a => [a] -> String
insertSpaces [] = ""
insertSpaces [x] = show x
insertSpaces (x:xs) = show x ++ " " ++ insertSpaces xs

texifySpaces :: Texable a => [a] -> String
texifySpaces [] = ""
texifySpaces [x] = texify x
texifySpaces (x:xs) = texify x ++ " " ++ texifySpaces xs

stringSpaces :: [String] -> String
stringSpaces [] = "\\ep"
stringSpaces [""] = "\\ep"
stringSpaces [x] = x
stringSpaces (x:xs) = ' ':(x ++ stringSpaces xs)

combine :: ([a], [a]) -> [a]
combine (x,y) = x++y

-- latex type
type Latex = String

class Show a => Texable a where
    texify :: a -> Latex
    texify = show

instance Texable String where
    texify = id

instance Texable VN where
    texify = show

instance (Texable a, Texable b) => Texable [(a,b)] where
    texify [] = ""
    texify ((j,k):rest) = texify j ++ "\\quad" ++ texify k ++ "\\\\" ++ texify rest

instance (Texable a) => Texable (a, Int) where
    texify (a,n) = texify a ++ replicate n '\''

-- tree printing functions

printTree :: Tree String -> IO ()
printTree t = putStrLn $ drawTree t

-- writes the LaTeX "forest" code to display the tree
latexTree :: Tree String -> IO ()
latexTree x = putStrLn $ "\n" ++ (unlines ("\\begin{forest}":(drawLatex x) ++ ["\\end{forest}"]))

latexNode :: String -> String
latexNode ('\n':xs) = "\\\\" ++ latexNode xs
latexNode ('\"':xs) = latexNode xs
latexNode ('\\':xs) = latexNode xs
latexNode ('#':xs) = "\\#" ++ latexNode xs
latexNode ('@':xs) = "\\ap" ++ latexNode xs
latexNode (';':xs) = "\\hgs{}" ++ latexNode xs
latexNode ('-':'W':'-':'>':xs) = "\\xra{W} " ++ latexNode xs
latexNode ('-':'C':'1':'-':'>':xs) = "\\xraa{C}{1} " ++ latexNode xs
latexNode ('-':'C':'2':'-':'>':xs) = "\\xraa{C}{2} " ++ latexNode xs
latexNode ('-':'C':'3':'-':'>':xs) = "\\xraa{C}{3} " ++ latexNode xs
latexNode ('-':'-':'>':xs) = "\\ra{} " ++ latexNode xs
latexNode ('-':'>':xs) = "\\ra{} " ++ latexNode xs
latexNode ('.':'.':xs) = latexNode xs
latexNode ('W':'h':xs) = "\\ml{wh}" ++ latexNode xs
latexNode ('V':'I':xs) = "V\\tul{I}" ++ latexNode xs
latexNode ('V':'E':xs) = "V\\tul{E}" ++ latexNode xs
latexNode ('~':xs) = "\\tripcat" ++ latexNode xs
latexNode (x:xs) = x : latexNode xs
latexNode "" = ""

drawLatex :: Tree String -> [String]
drawLatex (Node x []) = lines ("[{"++(x)++"}]")
drawLatex (Node x ts0) = lines ("[{"++(x)++"}") ++ drawSubTrees ts0 ++ ["]"]
    where
        drawSubTrees [] = []
        drawSubTrees (t:ts) =
            zipWith (++) (repeat "    ") (drawLatex t) ++ drawSubTrees ts

-------- basic categories ---------
-- nonterminals
data VN = S | T | U | R | A | B | C | D | CP | VP | NP | VE | VI | V | N deriving (Show, Eq)

-- terminals
type VT = String
  
{- -- not sure how this will work; the category of an LIG isn't nts... well... could replace with a var "cat", and cat = (nts,[ind])
class GF t y where
    category :: Tree t -> Maybe nts
    yield :: Tree t -> y

instance GF (LIGRule ll) String
-}

