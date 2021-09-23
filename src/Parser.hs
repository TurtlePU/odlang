{-# LANGUAGE OverloadedStrings #-}

module Parser where

import Data.Text (Text)
import Data.Void (Void)
import Text.Megaparsec
import qualified Text.Megaparsec.Char.Lexer as L
import Tree
import Text.Megaparsec.Char
import Data.List.NonEmpty (nonEmpty, toList)
import Data.List (foldl1')
import Data.Char (isAlpha, isAlphaNum)
import Control.Applicative (Applicative(liftA2))
import Data.Maybe (fromMaybe)
import Data.Functor (($>))

type Chunk = Text

type CustomError = Void

type ParseErrors = ParseErrorBundle Chunk CustomError

type Parser = Parsec CustomError Chunk

type InputType = Type

type InputTerm = Term Chunk

testParser = parseTest parser

parser :: Parser InputTerm
parser = between scn eof expr'
  where
    expr' = fromMaybe TmUnit <$> optional expr0
    expr = recoverWith TmUnit expr0
    expr0 = foldl1' TmApp <$> word `sepEndBy1` scn
    word = parens expr' <|> (var >>= liftA2 (<|>) finishAbs (pure . TmVar))
    finishAbs v = colon *> (TmAbs v <$> pType <* arrow <*> expr)
    pType = parens $ foldType <$> pType `sepBy` arrow
    var = lookAhead pBeginVar *> takeWhile1P Nothing contVar
    pBeginVar = label "variable" $ satisfy $ \c -> isAlpha c || c == '_'
    colon = lexeme ":" <?> "colon"
    arrow = lexeme "->" <?> "arrow"
    parens = between (lexeme "(") (lexeme ")")
    lexeme = between scn scn . chunk
    scn = L.space space1 lineComment blockComment
    lineComment = empty
    blockComment = empty
    contVar c = isAlphaNum c || c == '_'
    recoverWith defaultV = withRecovery $ ($> defaultV) . registerParseError
    foldType = maybe TyUnit (foldl1' TyArrow . toList) . nonEmpty
