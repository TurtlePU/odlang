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
  = TokWord Position Chunk
  | TokInside Position ParenKind (Maybe TokenTree)
  | TokConcat Position Separator (NonSingle TokenTree)

instance Show TokenTree where
  show (TokWord _ w) = show w
  show (TokInside _ k Nothing) = show k
  show (TokInside _ k (Just t)) = "TokInside " ++ show k ++ " " ++ show t
  show (TokConcat _ s ts) = "TokConcat " ++ show s ++ " " ++ show ts

data ParenKind = Paren | Bracket

instance Show ParenKind where
  show Paren = "( )"
  show Bracket = "[ ]"

data Separator = Space | None

instance Show Separator where
  show Space = show ' '
  show None = show ""

type Position = Int

type Chunk = Text

type Stream = Text

type CustomError = Void

type ParseErrors = ParseErrorBundle Stream CustomError

type Lexer = Parsec CustomError Stream

lexify = parse lexer

testLexer = parseTest lexer

lexer :: Lexer (Maybe TokenTree)
lexer = between scn eof expr
  where
    expr = tokConcat Space <$> getOffset <*> together `sepEndBy` scn
    together = tokConcat1 None <$> getOffset <*> togetherBody
    togetherBody = (:|) <$> callee <*> many inParens
    callee = TokWord <$> getOffset <*> (latinName <|> operatorName) <|> inParens
    latinName =
      (lookAhead (satisfy latinStart) <?> "ident start")
        *> takeWhile1P (Just "ident symbol") latinContent
    latinStart c = isAlpha c || c == '_'
    latinContent c = isAlphaNum c || c == '_'
    operatorName = someOf "operator symbol" "!#$%&*+.,;/<=>?@\\^|-~:"
    inParens = uncurry . TokInside <$> getOffset <*> (btw Paren <|> btw Bracket)
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

tokConcat :: Separator -> Position -> [TokenTree] -> Maybe TokenTree
tokConcat s p = fmap (tokConcat1 s p) . nonEmpty

tokConcat1 :: Separator -> Position -> NonEmpty TokenTree -> TokenTree
tokConcat1 s p = either id (TokConcat p s) . fromNonEmpty
