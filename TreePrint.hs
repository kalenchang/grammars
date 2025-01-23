module TreePrint where

import Prelude
import Data.Tree

-- rule showing functions
insertSpaces :: Show a => [a] -> String
insertSpaces [] = ""
insertSpaces (x:xs) = ' ':(show x ++ insertSpaces xs)

-- tree printing functions

printTree :: Tree String -> IO ()
printTree t = putStrLn $ drawTree t

-- writes the LaTeX "forest" code to display the tree
latexTree :: Tree String -> IO ()
latexTree x = putStrLn $ unlines $ ("\\begin{forest}":(drawLatex x) ++ ["\\end{forest}"])

latexNode :: String -> String
latexNode ('\n':xs) = "\\\\" ++ latexNode xs
latexNode (',':xs) = "\\hgs " ++ latexNode xs
latexNode ('-':'>':xs) = "\\ra " ++ latexNode xs
latexNode (x:xs) = x : latexNode xs
latexNode "" = ""

drawLatex :: Tree String -> [String]
drawLatex (Node x []) = lines ("[{"++(latexNode x)++"}]")
drawLatex (Node x ts0) = lines ("[{"++(latexNode x)++"}") ++ drawSubTrees ts0 ++ ["]"]
  where
    drawSubTrees [] = []
    drawSubTrees (t:ts) =
        zipWith (++) (repeat "    ") (drawLatex t) ++ drawSubTrees ts