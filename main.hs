import Data.List
import Data.Function

type Symb = String 

infix 1 `betaEq`, `alphaEq`
infixl 2 :@

data Expr = Var Symb
          | Expr :@ Expr
          | Lam Symb Expr
          deriving (Eq, Read, Show)-- компактно записанные переменные 

[a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z] = 
  map (Var . (:[])) "abcdefghijklmnopqrstuvwxyz"
-- аппликация двух аргументов
app2 f x y = f :@ x :@ y
-- аппликация трёх аргументов
app3 f x y z = f :@ x :@ y :@ z

-- комбинаторы
cI     = Lam "x" x
cK     = Lam "x" $ Lam "y" x
cK_ast = Lam "x" $ Lam "y" y
cB     = Lam "f" $ Lam "g" $ Lam "x" $ f :@ (g :@ x)
cS     = Lam "f" $ Lam "g" $ Lam "x" $ f :@ x :@ (g :@ x)

-- Булевы значения
fls = Lam "t" $ Lam "f" f
tru = Lam "t" $ Lam "f" t

iif = Lam "b" $ Lam "x" $ Lam "y" $ b :@ x :@ y

not' = Lam "b" $ Lam "t" $ Lam "f" $ app2 b f t
and' = Lam "x" $ Lam "y" $ app2 x y fls
or'  = Lam "x" $ Lam "y" $ app2 x tru y

-- пары
pair = Lam "x" $ Lam "y" $ Lam "f" $ app2 f x y

fst' = Lam "p" $ p :@ tru
snd' = Lam "p" $ p :@ fls

-- числа Чёрча
zero  = Lam "s" $ Lam "z" z
one   = Lam "s" $ Lam "z" $ s :@ z
two   = Lam "s" $ Lam "z" $ s :@ (s :@ z)
three = Lam "s" $ Lam "z" $ s :@ (s :@ (s :@ z))
four  = Lam "s" $ Lam "z" $ s :@ (s :@ (s :@ (s :@ z)))
five  = Lam "s" $ Lam "z" $ s :@ (s :@ (s :@ (s :@ (s :@ z))))
six   = Lam "s" $ Lam "z" $ s :@ (s :@ (s :@ (s :@ (s :@ (s :@ z)))))
seven = Lam "s" $ Lam "z" $ s :@ (s :@ (s :@ (s :@ (s :@ (s :@ (s :@ z))))))
eight = Lam "s" $ Lam "z" $ s :@ (s :@ (s :@ (s :@ (s :@ (s :@ (s :@ (s :@ z)))))))
nine  = Lam "s" $ Lam "z" $ s :@ (s :@ (s :@ (s :@ (s :@ (s :@ (s :@ (s :@ (s :@ z))))))))
ten   = Lam "s" $ Lam "z" $ s :@ (s :@ (s :@ (s :@ (s :@ (s :@ (s :@ (s :@ (s :@ (s :@ z)))))))))
  
iszro = Lam "n" $ n :@ (Lam "x" fls) :@ tru

suc = Lam "n" $ Lam "s" $ Lam "z" $  s :@ (n :@ s :@ z)

plus  = Lam "m" $ Lam "n" $ Lam "s" $ Lam "z" $ app2 m s (app2 n s z)

mult = Lam "m" $ Lam "n" $ Lam "s" $ m :@ (n :@ s)

pow = Lam "m" $ Lam "n" $ n :@ m

omega = Lam "x" $ x :@ x

zp = pair :@ zero :@ zero
sp = Lam "p" $  pair :@ (snd' :@ p) :@ (suc :@ (snd' :@ p))
pred' = Lam "m" $ fst' :@ (m :@ sp :@ zp)

-- факториал
zf = pair :@ one :@ zero
sf = Lam "p" $ pair :@ (mult :@ (fst' :@  p) :@ (suc :@ (snd' :@ p))) :@ (suc :@ (snd' :@ p))
fac = Lam "m" $ fst' :@ (m :@ sf :@ zf)

-- общая схема примитивной рекурсии
xz = Lam "x" $ pair :@ x :@ zero
fs = Lam "f" $ Lam "p" $ pair :@ (f :@ (fst' :@ p) :@ (snd' :@ p)) :@ (suc :@ (snd' :@ p))
rec = Lam "m" $ Lam "f" $ Lam "x" $ fst' :@ (m :@ (fs :@ f) :@ (xz :@ x))

pred'' = Lam "n" $ rec :@ n :@ cK_ast :@ zero

minus = Lam "k" $ Lam "l" $ l :@ pred' :@ k

lt = Lam "n" $ Lam "m" $ not' :@ (iszro :@ (minus :@ m :@ n))
ge = Lam "n" $ Lam "m" $  iszro :@ (app2 minus m n)
gt = Lam "n" $ Lam "m" $ not' :@ (iszro :@ (app2 minus n m))
le = Lam "n" $ Lam "m" $  iszro :@ (app2 minus n m)
eq = Lam "n" $ Lam "m" $ and' :@ (le :@ m :@ n) :@ (ge :@ m :@ n)

fac'step = Lam "u" $ Lam "v" $ app2 mult u (suc :@ v)
fac' = Lam "n" $ app3 rec n fac'step one

-- Y-комбинатор
cY = Lam "f" $ (Lam "z" $ f :@ (z :@ z)) :@ (Lam "z" $ f :@ (z :@ z)) 
cTheta = aa :@ aa 
  where aa = Lam "a" $ Lam "b" $ b :@ (a :@ a :@ b)

fac''step = Lam "f" $ Lam "n" $ iif :@ (iszro :@ n) :@ one :@ (mult :@ n :@ (f :@ (pred' :@ n))) 
fac''  =  cY :@ fac''step
fac''' = cTheta :@ fac''step

-- списки
nil  = Lam "c" $ Lam "n" n
cons = Lam "e" $ Lam "l" $ Lam "c" $ Lam "n" $ app2 c e (app2 l c n)

l532 = app2 cons five (app2 cons three (app2 cons two nil))
l2 = Lam "c" $ Lam "n" $ c :@ two :@ n

empty = Lam "l" $ app2 l (Lam "h" $ Lam "t" fls) tru

length' = Lam "l" $ app2 l (Lam "x" $ Lam "y" $ suc :@ y) zero
length'' = Lam "l" $ app2 l (Lam "y" $ suc) zero

head' = Lam "l" $ app2 l cK cI

zpl = app2 pair nil nil
spl = Lam "e" $ Lam "p" $ app2 pair (snd' :@ p) (app2 cons e (snd' :@ p))
tail' = Lam "l" $ fst' :@ (app2 l spl zpl)

sum' = Lam "l" $ app2 l plus zero
sum'' = Lam "l" $ app2 l (Lam "h" $ Lam "t" $ app2 plus h t) zero

-- 1 
freeVars :: Expr -> [Symb]
freeVars (Var x) = [x]
freeVars (lh :@ rh) = freeVars lh `union` freeVars rh
freeVars (Lam x expr) = nub (freeVars expr) \\ [x]
subst :: Symb -> Expr -> Expr -> Expr
subst symb what wher =
  let freeVarsWhat = freeVars what
      substWithList (t1 :@ t2) bound = substWithList t1 bound :@ substWithList t2 bound
      substWithList l@(Lam s ex) bound | symb `elem` freeVarsWhere && s `elem` freeVarsWhat = Lam (s ++ "'") $ substWithList ex $ s : bound
                                       | symb `elem` freeVarsWhere = Lam s $ substWithList ex bound
                                       | otherwise = l
        where freeVarsWhere = freeVars l
      substWithList v@(Var t) bound | symb == t && t `notElem` bound = what
                                  | symb /= t && t `elem` bound && t `elem` freeVarsWhat = Var $ t ++ "'"
                                  | otherwise = v
  in
    substWithList wher []
-- 2
alphaEq (Var v)   (Var v')    = v == v'
alphaEq (f :@ a) (f' :@ a') = alphaEq f f' && alphaEq a a'
alphaEq (Lam s e) (Lam s' e') = alphaEq e (subst s' (Var s) e') &&
    alphaEq e' (subst s (Var s') e)
alphaEq _ _ = False
   
-- main = print $ (Lam "x" $ Lam "y" $ Var "x") `alphaEq` (Lam "y" $ Lam "x" $ Var "y")

-- 3

reduceOnce :: Expr -> Maybe Expr
reduceOnce (Var v) = Nothing
reduceOnce ((Lam x expr) :@ arg) = Just $ subst x arg expr
reduceOnce (Lam x expr) = case reduceOnce expr of 
                            Nothing -> Nothing
                            Just rexpr -> Just $ Lam x rexpr
reduceOnce (lh :@ rh) = 
    case reduceOnce lh of 
      Just rlh -> Just $ rlh :@ rh
      Nothing -> case reduceOnce rh of 
                   Just rrh -> Just $ lh :@ rrh
                   Nothing -> Nothing
-- main = print (
--             reduceOnce $ Lam "x" $ Lam "y" $ Var "x",
--             reduceOnce $ Lam "x" $ Lam "y" $ (Lam "z" $ Var "z") :@ Var "x",
--             let omega = Lam "x" $ Var "x" :@ Var "x" in reduceOnce $ omega :@ omega
--              )

-- 4 
nf :: Expr -> Expr
nf expr = maybe expr nf (reduceOnce expr) 

-- main = print (
--     nf (fac :@ three) `alphaEq` six,
--     nf (Var "x" :@ Var "y") `alphaEq` (Var "x" :@ Var "y"),
--     nf tru `alphaEq` cK,
--     nf (pred' :@ two) `alphaEq` one,
--     nf (fac :@ three) `alphaEq` six,
--     nf (length' :@ (tail' :@ l532)) `alphaEq` two,
--     nf (omega :@ three) `alphaEq` nf (minus :@ (mult :@ seven :@ five) :@ eight)
--  )

-- 5
betaEq :: Expr -> Expr -> Bool 
betaEq a b = nf a `alphaEq` nf b

main = print $ (fac :@ three) `betaEq` six
