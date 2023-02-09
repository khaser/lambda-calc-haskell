import Data.List
import Data.Function
import Control.Monad (unless)
import System.IO
import Control.Applicative
import Data.Bifunctor (first,second)
import Data.Char (isLetter, isDigit, isSpace)

type Symb = String 

infixl 2 :@

data Expr = Var Symb
          | Expr :@ Expr
          | Lam Symb Expr
          deriving Eq

-- Reducing
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

nf :: Expr -> Expr
nf expr = maybe expr nf (reduceOnce expr) 

-- Parsing 
instance Show Expr where
  show (Var x) = x
  show (Lam x expr) = "\\" ++ x ++ " -> " ++ show expr
  show (lh :@ rh) = wrap lh ++ " " ++ wrap rh
      where 
          wrap hand = case hand of 
              Var x -> x
              _ -> "(" ++ show hand ++ ")"

newtype Parser a = Parser { runParse :: String -> [(a, String)] }

instance Functor Parser where
  fmap f (Parser p) = Parser (map (first f) . p)

instance Applicative Parser where
    pure x = Parser (\s -> [(x,s)])
    (<*>) f a = Parser (\s -> [ (f x, f_x_tail) | 
                                            (f, f_tail) <- runParse f s,
                                            (x, f_x_tail) <- runParse a f_tail])

instance Alternative Parser where
    (<|>) parse_a parse_b = Parser (\s -> runParse parse_a s ++ runParse parse_b s )
    empty = Parser (const [])

exprParser :: Parser Expr
exprParser = foldl1 (:@) <$> some (subTerm <* getC ' ' <|> subTerm)
    where
        subTerm = wrapParser exprParser <|> lambdaParser <|> (Var <$> varParser)

lambdaParser :: Parser Expr
lambdaParser = getStr "\\" *> longLambdaParser 

longLambdaParser :: Parser Expr
longLambdaParser = (Lam <$> varParser <* getC ' ') <*> 
                     ((getStr "-> " *> exprParser <* endTerm) <|> longLambdaParser)
                         where endTerm = peekC ')'

wrapParser :: Parser a -> Parser a
wrapParser parser = getC '(' *> parser <* getC ')'

varParser :: Parser String
varParser = (const . foldr (:) "" <$> some (ensureP varChar)) <*> 
    peekP (\x -> x == ')' || x == ' ')
    where 
        varChar x = isDigit x || isLetter x

ensureP :: (Char -> Bool) -> Parser Char
ensureP pred = Parser func 
    where 
        func (shead : stail) = [(shead, stail) | pred shead]
        func [] = []

getC :: Char -> Parser Char 
getC c = ensureP (== c)

peekP :: (Char -> Bool) -> Parser () 
peekP p = Parser func
    where 
        func s@(shead:_) = [((), s) | p shead]
        func [] = [((), [])]

peekC c = peekP (==c)

getStr :: String -> Parser String
getStr expected = Parser func
    where 
        func str = [(expected, drop (length expected) str) | expected `isPrefixOf` str]

instance Read Expr where
  readsPrec prec = runParse exprParser

-- REPL
readWithPrompt :: IO String
readWithPrompt = do
    putStr "Expr> "
    hFlush stdout
    getLine

main = do
  input <- readWithPrompt
  unless (input == ":quit") $ print (nf $ read input) >> main
