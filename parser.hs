import Control.Applicative
import Data.Bifunctor (first,second)
import Data.List (isPrefixOf)
import Data.Char (isLetter, isDigit, isSpace)

type Symb = String 

infixl 2 :@

data Expr = Var Symb
          | Expr :@ Expr
          | Lam Symb Expr
              deriving Eq

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
 
cY = let {x = Var "x"; f = Var "f"; fxx = Lam "x" $ f :@ (x :@ x)} in Lam "f" $ fxx :@ fxx

main = print (
    -- runParse exprParser "\\f -> (\\x -> f (x x)) (\\x -> f (x x))"
    -- read "\\f -> (\\x -> f (x x)) (\\x -> f (x x))" :: Expr
    -- \\f -> (\\x -> f (x x)) (\\x -> f (x x))
    -- read "(\\x -> y)" :: Expr
    -- runParse exprParser "\\x1 x2 -> x3 x4 x5"
    -- show $ Lam "x" (Var "x" :@ Var "y"),
    -- show cY,
    (read "\\x1 x2 -> x1 x2 x2" :: Expr) == Lam "x1" (Lam "x2" (Var "x1" :@ Var "x2" :@ Var "x2")),
    read (show cY) == cY
       )
