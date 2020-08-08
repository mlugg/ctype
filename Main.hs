{-# LANGUAGE OverloadedStrings, LambdaCase #-}

module Main where

import Text.Megaparsec
import Text.Megaparsec.Char
import Control.Monad.Combinators.Expr
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Text(Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Void
import Data.Functor
import Data.List
import Data.Maybe

lookup' :: (Eq a) => a -> b -> [(a, b)] -> b
lookup' k z = fromMaybe z . lookup k

data Signedness = Signed | Unsigned
  deriving (Show)

data IntSize
  = I8
  | I16
  | I32
  | I64
  deriving (Show)

data FloatSize
  = F32
  | F64
  | F80
  deriving (Show)

data Qualifiers = Qualifiers
  { qualConst :: Bool
  , qualVolatile :: Bool
  } deriving (Show)

qualifiersNone = Qualifiers False False

instance Semigroup Qualifiers where
  Qualifiers c0 v0 <> Qualifiers c1 v1 = Qualifiers (c0 || c1) (v0 || v1)

instance Monoid Qualifiers where
  mempty = qualifiersNone

data Type
  = TVoid Qualifiers
  | TInt Qualifiers IntSize Signedness
  | TFloat Qualifiers FloatSize
  | TPtr Qualifiers Type
  | TFunc [(Maybe Text, Type)] Type
  | TArray (Maybe Integer) Type
  | TEnum Text
  | TStruct Text
  | TUnion Text
  deriving (Show)

data TExpr
  = TEName Text
  | TENoName
  | TEDeref Qualifiers TExpr
  | TECall [(Maybe Text, Type)] TExpr
  | TEIndex (Maybe Integer) TExpr
  deriving (Show)

texprToType :: Type -> TExpr -> (Maybe Text, Type)
texprToType t e = case e of
  TEName x -> (Just x, t)
  TENoName -> (Nothing, t)
  TEDeref qs e0 -> texprToType (TPtr qs t) e0
  TECall as e0 -> texprToType (TFunc as t) e0
  TEIndex i e0 -> texprToType (TArray i t) e0

type Parser = Parsec Void Text

-- Utility parsers {{{

lineComment :: Parser ()
lineComment = L.skipLineComment "//"
blockComment :: Parser ()
blockComment = L.skipBlockComment "/*" "*/"

sc :: Parser ()
sc = L.space space1 lineComment blockComment

symbol :: Text -> Parser Text
symbol = L.symbol sc

decimal :: (Num a) => Parser a
decimal = L.decimal <* sc

parens   = between (symbol "(") (symbol ")")
brackets = between (symbol "[") (symbol "]")
braces   = between (symbol "{") (symbol "}")
comma  = symbol ","
equals = symbol "="
 
-- }}}

-- Identifiers {{{

reservedWords :: [Text]
reservedWords =
  [ "auto", "break", "case", "char", "const", "continue", "default"
  , "do", "double", "else", "enum", "extern", "float", "for", "goto"
  , "if", "int", "long", "register", "return", "short", "signed"
  , "sizeof", "static", "struct", "switch", "typedef", "union"
  , "unsigned", "void", "volatile", "while" ]


ident :: Parser Text
ident = do
  x <- letterChar <|> char '_'
  xs <- many $ alphaNumChar <|> char '_'
  sc
  let xs' = T.pack $ x:xs
  if xs' `elem` reservedWords
  then empty <?> "identifier"
  else pure xs'

-- }}}

-- Qualifiers {{{

qual :: Parser Qualifiers
qual = qualifiersNone{qualConst=True} <$ symbol "const"
   <|> qualifiersNone{qualVolatile=True} <$ symbol "volatile"

quals :: Parser Qualifiers
quals = mconcat <$> many qual

qualsAround :: Parser a -> Parser (a, Qualifiers)
qualsAround p = f <$> quals <*> p <*> quals
  where f q0 x q1 = (x, q0 <> q1)

-- }}}

-- Numeric type parsing (numType) {{{

-- FUCK C
-- This is pretty gross and weird, but it's the simplest way I could
-- think to do it
numType :: Parser Type
numType = some (qualsAround intWord) <&> count >>= constructType
  where intWord = symbol "char"
              <|> symbol "int"
              <|> symbol "long"
              <|> symbol "short"
              <|> symbol "signed"
              <|> symbol "unsigned"
              <|> symbol "float"
              <|> symbol "double"

        count xs =
          let xs' = fst <$> xs
              qs = mconcat $ snd <$> xs
              counted = fmap (\gr -> (head gr, length gr)) $ group $ sort xs'
              f x = lookup' x 0 counted
              counts = (f "char", f "int", f "long", f "short", f "signed", f "unsigned", f "float", f "double")
          in (counts, qs)

        constructType (x,qs) = case x of
          -- char
          (1,0,0,0,0,0,0,0) -> f I8 Signed
          (1,0,0,0,1,0,0,0) -> f I8 Signed
          (1,0,0,0,0,1,0,0) -> f I8 Unsigned
          -- short
          (0,0,0,1,0,0,0,0) -> f I16 Signed
          (0,0,0,1,1,0,0,0) -> f I16 Signed
          (0,1,0,1,0,0,0,0) -> f I16 Signed
          (0,1,0,1,1,0,0,0) -> f I16 Signed
          (0,0,0,1,0,1,0,0) -> f I16 Unsigned
          (0,1,0,1,0,1,0,0) -> f I16 Unsigned
          -- int
          (0,1,0,0,0,0,0,0) -> f I32 Signed
          (0,0,0,0,1,0,0,0) -> f I32 Signed
          (0,1,0,0,1,0,0,0) -> f I32 Signed
          (0,0,0,0,0,1,0,0) -> f I32 Unsigned
          (0,1,0,0,0,1,0,0) -> f I32 Unsigned
          -- long
          (0,0,1,0,0,0,0,0) -> f I64 Signed
          (0,0,1,0,1,0,0,0) -> f I64 Signed
          (0,1,1,0,0,0,0,0) -> f I64 Signed
          (0,1,1,0,1,0,0,0) -> f I64 Signed
          (0,0,1,0,0,1,0,0) -> f I64 Unsigned
          (0,1,1,0,0,1,0,0) -> f I64 Unsigned
          -- long long
          (0,0,2,0,0,0,0,0) -> f I64 Signed
          (0,0,2,0,1,0,0,0) -> f I64 Signed
          (0,1,2,0,0,0,0,0) -> f I64 Signed
          (0,1,2,0,1,0,0,0) -> f I64 Signed
          (0,0,2,0,0,1,0,0) -> f I64 Unsigned
          (0,1,2,0,0,1,0,0) -> f I64 Unsigned
          -- float
          (0,0,0,0,0,0,1,0) -> pure $ TFloat qs F32
          -- double
          (0,0,0,0,0,0,0,1) -> pure $ TFloat qs F64
          -- long double
          (0,0,1,0,0,0,0,1) -> pure $ TFloat qs F80

          _ -> fail "Invalid num type"

          where f x y = pure $ TInt qs x y

-- }}}

simpleType :: Parser Type
simpleType = TVoid . snd <$> try (qualsAround $ symbol "void")
         <|> TEnum <$> (symbol "enum" *> ident)
         <|> TStruct <$> (symbol "struct" *> ident)
         <|> TUnion <$> (symbol "union" *> ident)
         <|> numType

-- The expr parser by default does not allow chaining of unary ops of
-- same precendence, so the weird folds in the op table here are making
-- that work
typeExpr :: Parser TExpr
typeExpr = makeExprParser term
  [ [ Postfix $ foldr1 (flip (.)) <$> some postfix ]
  , [ Prefix $ foldr1 (.) <$> some prefix ] ]
  where
    term = parens typeExpr
       <|> TEName <$> ident
       <|> pure TENoName

    postfix = funcCall <|> arrIndex
    prefix = ptrDeref
    funcCall = TECall <$> parens (typeOrDecl `sepBy` comma)
    arrIndex = TEIndex <$> brackets (optional decimal)
    ptrDeref = TEDeref <$> (symbol "*" *> quals)

typeOrDecl :: Parser (Maybe Text, Type)
typeOrDecl = texprToType <$> simpleType <*> typeExpr

-- Pretty-printing {{{

pPrintQuals :: Qualifiers -> Text
pPrintQuals (Qualifiers c v) = T.concat
  [ if c then "const " else ""
  , if v then "volatile " else "" ]

pPrintInt :: IntSize -> Signedness -> Text
pPrintInt sz s = s' <> " " <> sz'
  where
    s' = case s of
      Signed -> "signed"
      Unsigned -> "unsigned"
    sz' = case sz of
      I8 -> "int8"
      I16 -> "int16"
      I32 -> "int32"
      I64 -> "int64"

pPrintFloat :: FloatSize -> Text
pPrintFloat sz = case sz of
  F32 -> "float32"
  F64 -> "float64"
  F80 -> "float80"

pPrintArg :: (Maybe Text, Type) -> Text
pPrintArg (Just x, t) = x <> " as " <> pPrintCType t
pPrintArg (Nothing, t) = pPrintCType t

pPrintCType :: Type -> Text
pPrintCType t = case t of
  TVoid qs -> pPrintQuals qs <> "void"
  TInt qs sz s -> pPrintQuals qs <> pPrintInt sz s
  TFloat qs sz -> pPrintQuals qs <> pPrintFloat sz
  TPtr qs t0 -> pPrintQuals qs <> "pointer to " <> pPrintCType t0
  TFunc as t0 -> "function (" <> T.intercalate ", " (pPrintArg <$> as) <> ") returning " <> pPrintCType t0
  TArray (Just i) t -> "array " <> T.pack (show i) <> " of " <> pPrintCType t
  TArray Nothing t -> "array of " <> pPrintCType t
  TEnum x -> "enum " <> x
  TStruct x -> "struct " <> x
  TUnion x -> "union " <> x

-- }}}

main :: IO ()
main =
  TIO.getLine <&>
  parse typeOrDecl "(stdin)" >>=
  \case
    Left e -> putStrLn $ errorBundlePretty e
    Right (x, t) -> do
      case x of
        Nothing -> pure ()
        Just x' -> TIO.putStr $ "declare " <> x' <> " as "
      TIO.putStrLn $ pPrintCType t
