{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Control.Applicative (Applicative (liftA2))
import Control.Monad ((>=>))
import Data.Bifunctor (first)
import Data.Char (isAlpha, isAlphaNum)
import Data.Functor (($>))
import Data.List (foldl1')
import Data.List.NonEmpty (nonEmpty, toList)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Tree

type Chunk = Text

type CustomError = Void

type ParseErrors = ParseErrorBundle Chunk CustomError

type Parser = Parsec CustomError Chunk

type Offset = Int

type InputType = Type Offset

type InputTerm = Term Offset Chunk

testParser = parseTest parser

parser :: Parser InputTerm
parser = between scn eof $ mbExpr Nothing

mbExpr :: Maybe Offset -> Parser InputTerm
mbExpr (Just o) = maybe (TmUnit o) (first (const o)) <$> optional expr
mbExpr Nothing = optional expr >>= maybe (TmUnit <$> getOffset) pure

expr :: Parser InputTerm
expr = foldl1' tmApp <$> word `sepEndBy1` scn
  where
    tmApp f x = TmApp (tmInfo f) f x

word :: Parser InputTerm
word = parens (mbExpr . Just) <|> (var >>= liftA2 (<|>) finishAbs appVar)
  where
    appVar = pure . uncurry TmVar

finishAbs :: (Offset, Chunk) -> Parser InputTerm
finishAbs (o, v) = colon *> (TmAbs o v <$> pType <* arrow <*> expr)

pType = parens ptype
  where
    ptype o = recoverWith (TyUnit o) $ foldType o <$> pType `sepBy` arrow

var :: Parser (Offset, Chunk)
var = (,) <$> getOffset <*> (lookAhead pBeginVar *> takeWhile1P Nothing contVar)

contVar c = isAlphaNum c || c == '_'

pBeginVar = label "variable" $ satisfy $ \c -> isAlpha c || c == '_'

colon = lexeme ":"

arrow = lexeme "->"

parens :: (Offset -> Parser a) -> Parser a
parens p = getOffset >>= between (lexeme "(") (lexeme ")") . p

lexeme = try . between scn scn . chunk

scn = L.space space1 lineComment blockComment

lineComment = empty

blockComment = empty

recoverWith defaultV = withRecovery $ ($> defaultV) . registerParseError

foldType o = maybe (TyUnit o) (foldl1' (TyArrow o) . toList) . nonEmpty
