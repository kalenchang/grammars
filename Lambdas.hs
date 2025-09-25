module Lambdas where
-- from Oleg Kiselyov

import Prelude hiding ((^))
import Printing

type VColor = Int  -- the "color" of a variable. 0 is the "transparent color"
data VarName = VC VColor String deriving (Eq)

data Term = Var VarName | Ap Term Term | Lm VarName Term 
             deriving Eq

eval term = eval' term []
eval' t@(Var v) [] = t
eval' (Lm v body) [] = check_eta $ Lm v (eval body)
eval' (Lm v body) (t: rest) = eval' (subst body v t) rest
eval' (Ap t1 t2) stack = eval' t1 (t2:stack)
eval' t@(Var v) stack = unwind t stack

unwind t [] = t
unwind t (t1:rest) = unwind (Ap t $ eval t1) rest

subst term v (Var v') | v == v' = term -- identity substitution
subst t@(Var x) v st | x == v    = st
           | otherwise = t
subst (Ap t1 t2) v st = Ap (subst t1 v st) $ (subst t2 v st)
subst t@(Lm x _) v _ | v == x  = t
subst (Lm x body) v st = (Lm x' (subst body' v st)) 
    where
        (f,x_occur_st) = occurs st x
        (x',body') =
            if f then 
                let x_uniq_st_v = bump_color' (bump_color x x_occur_st) v
                    (bf,x_occur_body) = occurs body x_uniq_st_v
                    x_unique = if bf
                                then bump_color x_uniq_st_v x_occur_body 
                                else x_uniq_st_v
                   in (x_unique,subst body x (Var x'))
            else (x,body)
        bump_color (VC color name) (VC color' _) = 
                                     (VC ((max color color')+1) name)
        bump_color' v1@(VC _ name) v2@(VC _ name') = 
                   if name==name' then bump_color v1 v2 else v1

occurs (Var v'@(VC c' name')) v@(VC c name)
    | not (name == name')  = (False, v)
    | c == c'              = (True, v)
    | otherwise            = (False,v')
occurs (Ap t1 t2) v = let (f1,v1@(VC c1 _)) = occurs t1 v
                          (f2,v2@(VC c2 _)) = occurs t2 v
                     in (f1 || f2, if c1 > c2 then v1 else v2)
occurs (Lm x body) v | x == v    = (False,v)
                    | otherwise = occurs body v

check_eta (Lm v (Ap t (Var v')))
      | v == v' && (let (flag,_) = occurs t v in not flag) = t
check_eta term = term

make_var = Var . VC 0
[x,y,z,f,g,h,k,p,q] = map make_var ["x","y","z","f","g","h","k","p","q"]

infixl 8 # 
(#) = Ap
infixr 6 ^      -- a better notation for a lambda-abstraction
(Var v) ^ body = Lm v body

instance Show VarName where
   show (VC color name) = if color == 0 then name 
                                         else name ++ "_" ++ (show color)

show_term (Var v) _ = show v       -- show the variable regardless of depth
show_term _ depth | depth <= 0 = "..."
show_term term depth = showt term
 where
   showt (Lm v body) = "(\\" ++ (show v) ++ ". " ++ (showt' body) ++ ")"
   showt (Ap t1 t2@(Ap _ _)) = (showt' t1) ++ " " ++ "(" ++ (showt' t2) ++ ")"
   showt (Ap t1 t2) = (showt' t1) ++ " " ++ (showt' t2)
   showt' term = show_term term (depth - 1)

instance Show Term where
   show term = show_term term 10

------- new stuff
instance Texable VarName where
    texify = show

instance Texable Term where
    texify term = lambdatex $ show_term term 10

lambdatex ('\\':xs) = "\\lam " ++ lambdatex xs
lambdatex ('.':xs) = "\\dt " ++ lambdatex xs
lambdatex (x:xs) = x:(lambdatex xs)
lambdatex [] = []


lookupint ((x,int):xs) r = if x == r then int else lookupint xs r

idterm = x ^ x
lfa = x ^ y ^ y # x
rfa = x ^ y ^ x # y
funccomp = x ^ y ^ z ^ x # (y # z)

[mary', john', let', run', swim'] = map make_var ["mary'", "john'", "let'", "run'", "swim'"]

-- todo: i think i need to figure out how to convert these lambda terms to haskell functions, so that
--      i can evaluate things like arithmetic or tree building or string concat or list building, because
--      eval can only do beta/eta reduction
-- but what would i show? because i can't always show the haskell result, but the lambda result won't always be fully simplified
-- feels like i really need a better way to show haskell functions......
-- or ... idk recreate list building in this lambda stuff?