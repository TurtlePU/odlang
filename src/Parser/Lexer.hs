{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Parser.Lexer where

import Control.Applicative (Alternative (empty, (<|>)), liftA2)
import Control.Monad (void)
import Data.Char (isAlpha, isAlphaNum)
import Data.List.NonEmpty (NonEmpty ((:|)), nonEmpty)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Void (Void)
import NonSingle
import Text.Megaparsec hiding (Stream)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

data TokenTree
  = TokWord Stream
  | TokInside ParenKind (Maybe TokenTree)
  | TokConcat Separator (NonSingle TokenTree)

data ParenKind = Paren | Bracket

data Separator = Newline | Space | None

type Stream = Text

type CustomError = Void

type ParseErrors = ParseErrorBundle Stream CustomError

type Lexer = Parsec CustomError Stream

lexify :: String -> Text -> Either ParseErrors TokenTree
lexify = parse $ L.nonIndented scn tree <* eof
  where
    tree = indentBlock $ mergeTo <$> spaced
    mergeTo s Nothing = s
    mergeTo (TokConcat Space s) (Just t) = TokConcat Space (s |> t)
    mergeTo s (Just t) = TokConcat Space [s, t]

indentBlock :: Lexer (Maybe TokenTree -> a) -> Lexer a
indentBlock f = L.indentBlock scn $ merger <$> f
  where
    merger f = L.IndentMany Nothing (pure . f . tokConcat Newline) spaced

spaced :: Lexer TokenTree
spaced = unwrap . tokConcat Space <$> sepEndBy1 together sc

together :: Lexer TokenTree
together = tokConcat1 None <$> liftA2 (:|) callee (many inParens)

callee :: Lexer TokenTree
callee = TokWord <$> (latinName <|> operatorName) <|> inParens

inParens :: Lexer TokenTree
inParens = uncurry TokInside <$> (btw Paren <|> btw Bracket)
  where
    btw p = (p,) <$> between (open p) (close p) (indentBlock $ pure id)
    open p = single (op p) *> scn
    close p = scn *> single (cl p)
    op Paren = '('
    op Bracket = '['
    cl Paren = ')'
    cl Bracket = ']'

latinName :: Lexer Text
latinName = lookAhead (satisfy begin) *> takeWhileP Nothing content
  where
    begin c = isAlpha c || c == '_'
    content c = isAlphaNum c || c == '_'

operatorName :: Lexer Text
operatorName = takeWhile1P Nothing content
  where
    content c = c `elem` ("!#$%&*+./<=>?@\\^|-~:" :: String)

scn :: Lexer ()
scn = mySpace " \r\n"

sc :: Lexer ()
sc = mySpace " "

mySpace :: String -> Lexer ()
mySpace s = L.space (void $ oneOf s) lineComment blockComment

lineComment :: Lexer ()
lineComment = empty

blockComment :: Lexer ()
blockComment = empty

tokConcat :: Separator -> [TokenTree] -> Maybe TokenTree
tokConcat s = fmap (tokConcat1 s) . nonEmpty

tokConcat1 :: Separator -> NonEmpty TokenTree -> TokenTree
tokConcat1 s = either id (TokConcat s) . fromNonEmpty

unwrap :: Maybe a -> a
unwrap = fromMaybe undefined
