{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Parser.Lexer where

import Control.Applicative (Alternative (empty, (<|>)), liftA2)
import Control.Monad (void)
import Data.Char (isAlpha, isAlphaNum)
import Data.List.NonEmpty (NonEmpty ((:|)), nonEmpty)
import Data.Text (Text)
import Data.Void (Void)
import NonSingle
import Text.Megaparsec hiding (Stream)
import qualified Text.Megaparsec.Char.Lexer as L

data TokenTree
  = TokWord Stream
  | TokInside ParenKind (Maybe TokenTree)
  | TokConcat Separator (NonSingle TokenTree)

instance Show TokenTree where
  show (TokWord w) = show w
  show (TokInside k Nothing) = show k
  show (TokInside k (Just t)) = "TokInside " ++ show k ++ " " ++ show t
  show (TokConcat s ts) = "TokConcat " ++ show s ++ " " ++ show ts

data ParenKind = Paren | Bracket

instance Show ParenKind where
  show Paren = "( )"
  show Bracket = "[ ]"

data Separator = Space | None

instance Show Separator where
  show Space = show ' '
  show None = show ""

type Stream = Text

type CustomError = Void

type ParseErrors = ParseErrorBundle Stream CustomError

type Lexer = Parsec CustomError Stream

lexify = parse lexer

testLexer = parseTest lexer

lexer :: Lexer (Maybe TokenTree)
lexer = between scn eof expr
  where
    expr = tokConcat Space <$> together `sepEndBy` scn
    together = tokConcat1 None <$> liftA2 (:|) callee (many inParens)
    callee = TokWord <$> (latinName <|> operatorName) <|> inParens
    latinName =
      (lookAhead (satisfy latinStart) <?> "ident start")
        *> takeWhile1P (Just "ident symbol") latinContent
    latinStart c = isAlpha c || c == '_'
    latinContent c = isAlphaNum c || c == '_'
    operatorName = someOf "operator symbol" "!#$%&*+.,;/<=>?@\\^|-~:"
    inParens = uncurry TokInside <$> (btw Paren <|> btw Bracket)
    btw p = (p,) <$> between (single (op p) *> scn) (scn <* single (cl p)) expr
    scn = L.space (void $ someOf "whitespace" " \r\n") lineComment blockComment
    lineComment = empty
    blockComment = empty
    someOf :: String -> String -> Lexer Text
    someOf name variants = takeWhile1P (Just name) (`elem` variants)

op :: ParenKind -> Char
op Bracket = '['
op Paren = '('

cl :: ParenKind -> Char
cl Bracket = ']'
cl Paren = ')'

tokConcat :: Separator -> [TokenTree] -> Maybe TokenTree
tokConcat s = fmap (tokConcat1 s) . nonEmpty

tokConcat1 :: Separator -> NonEmpty TokenTree -> TokenTree
tokConcat1 s = either id (TokConcat s) . fromNonEmpty
