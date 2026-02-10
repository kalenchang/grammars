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

free_vars:: Term -> [VarName]
free_vars term = free_vars' term [] []
   where -- free_vars' term list-of-bound-vars list-of-free-vars-so-far
    free_vars' (Var v) bound free = if v `elem` bound then free else v:free
    free_vars' (Ap t1 t2) bound free = free_vars' t1 bound $ free_vars' t2 bound free
    free_vars' (Lm v body) bound free = free_vars' body (v:bound) free

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
   show term = show_term term 30

------- new stuff
instance Texable VarName where
    texify v = show v

funcify v = "\\func{" ++ show v ++ "}"

instance Texable Term where
    texify term = '$':(tex_term term 10 (free_vars term)) ++ "$"
tex_term (Var v) _ frees = if elem v frees then funcify v else texify v       
tex_term _ depth frees | depth <= 0 = "..."
tex_term term depth frees = texit term frees
 where
   texit (Lm v body) fs = "(\\lam " ++ (show v) ++ "\\dt " ++ (texit' body fs) ++ ")"
   texit (Ap t1 t2@(Ap _ _)) fs = (texit' t1 fs) ++ " " ++ "(" ++ (texit' t2 fs) ++ ")"
   texit (Ap t1 t2) fs = (texit' t1 fs) ++ "\\, " ++ (texit' t2 fs)
   texit' term fs = tex_term term (depth - 1) fs

-- instance Texable Term where
--     texify term = '$':(lambdatex $ show_term term 10) ++ "$"
-- lambdatex ('\\':xs) = "\\lam " ++ lambdatex xs
-- lambdatex ('.':xs) = "\\dt " ++ lambdatex xs
-- lambdatex (x:xs) = x:(lambdatex xs)
-- lambdatex [] = []


lookupint ((x,int):xs) r = if x == r then int else lookupint xs r

idterm = x ^ x
lfa = x ^ y ^ y # x
rfa = x ^ y ^ x # y
funccomp = x ^ y ^ z ^ x # (y # z)
bcomb = f ^ g ^ k ^ g # (f # k)
lowerid = g ^ g # (idterm)
binop = x ^ y ^ z ^ y # x # z
posslink = x ^ y ^ z ^ z # x

[mary', john', let', run', swim', up', flr', no', neighbor'] = map make_var ["m", "j", "let", "run", "swim", "up", "flr", "no", "nb"]
[n1', n2', n3', plus', times', minus'] = map make_var ["1", "2", "3", "+", "*", "-"]

-- holdout n lambda arguments
holdout :: Int -> Term
holdout 0 = f ^ k ^ k # f
holdout n = if n > 0 then eval $ (g ^ f ^ k ^ x ^ g # (f # x) # k) # (holdout $ n-1)
                     else undefined

-- reverse the order of the first n lambda abstractions
-- revlam :: Int -> Term -> Term
revlam n t = revlam' n t id
revlam' 0 t f = f t
revlam' n (Lm v b) f = revlam' (n-1) b (\x -> Lm v (f x))

-- f is the original mu, x is the daughter to toss (lexical), y is for func comp
-- pctterm 0 = f ^ x ^ y ^ f # y
-- pctterm 1 = f ^ x ^ x_1 ^ y ^ x_1 # (f # y)
-- pctterm 2 = f ^ x ^ x_1 ^ x_2 ^ y ^ x_2 # (x_1 # (f # y))

pctterm n = f ^ (revlam (n+2) (y ^ (pcttermfst n (pcttermsec n))))

pcttermfst 0 rest = x ^ rest
pcttermfst n rest = Lm (VC n "x") (pcttermfst (n-1) rest)

pcttermsec 0 = f # y
pcttermsec n = Var (VC n "x") # (pcttermsec $ n-1)


-- lreloop 0 = f ^ k ^ x ^ k # (f # x)
-- lreloop 1 = f ^ p ^ k ^ x ^ k # (f # x # p)
-- lreloop 2 = f ^ p ^ q ^ k ^ x ^ k # (f # x # p # q)

lreloop n = f ^ (revlam n (lreendfst n (k ^ y ^ (k # (lreendsnd n (f # y))))))

-- lreend 0 = f ^ k ^ k # f
-- lreend 1 = f ^ p ^ k ^ k # (f # p)
-- lreend 2 = f ^ p ^ q ^ k ^ k # (f # p # q)

lreend n = f ^ (revlam n (lreendfst n (k ^ (k # (lreendsnd n f)))))

lreendfst 0 rest = rest
lreendfst n rest = Lm (VC n "x") (lreendfst (n-1) rest)

lreendsnd 0 f = f
lreendsnd n f = (lreendsnd (n-1) f) # Var (VC n "x")

-- todo: i think i need to figure out how to convert these lambda terms to haskell functions, so that
--      i can evaluate things like arithmetic or tree building or string concat or list building, because
--      eval can only do beta/eta reduction
-- but what would i show? because i can't always show the haskell result, but the lambda result won't always be fully simplified
-- feels like i really need a better way to show haskell functions......
-- or ... idk recreate list building in this lambda stuff?