module TreePrint where

import Prelude
import Data.Tree

-- rule showing functions
insertSpaces :: Show a => [a] -> String
insertSpaces [] = ""
insertSpaces (x:xs) = ' ':(show x ++ insertSpaces xs)

combine :: ([a], [a]) -> [a]
combine (x,y) = x++y

-- tree printing functions

printTree :: Tree String -> IO ()
printTree t = putStrLn $ drawTree t

-- writes the LaTeX "forest" code to display the tree
latexTree :: Tree String -> IO ()
latexTree x = putStrLn $ unlines $ ("\\begin{forest}":(drawLatex x) ++ ["\\end{forest}"])

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
latexNode ('V':'E':xs) = "V\\tul{E}" ++ latexNode xs
latexNode (x:xs) = x : latexNode xs
latexNode "" = ""

drawLatex :: Tree String -> [String]
drawLatex (Node x []) = lines ("[{"++(latexNode x)++"}]")
drawLatex (Node x ts0) = lines ("[{"++(latexNode x)++"}") ++ drawSubTrees ts0 ++ ["]"]
    where
        drawSubTrees [] = []
        drawSubTrees (t:ts) =
            zipWith (++) (repeat "    ") (drawLatex t) ++ drawSubTrees ts

-------- basic categories ---------
-- nonterminals
data VN = S | T | U | R | A | B | C | D deriving (Show, Eq)

-- terminals
type VT = String
  
{- -- not sure how this will work; the category of an LIG isn't nts...
class GF t y where
    category :: Tree t -> Maybe nts
    yield :: Tree t -> y

instance GF (LIGRule ll) String
-}

