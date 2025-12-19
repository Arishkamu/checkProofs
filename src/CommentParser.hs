module CommentParser (cmtParsed, Comment) where

import Text.Parsec
import Text.Parsec.String (Parser)
import Data.Char (chr)

data Comment = Line Int String | Block String
  deriving (Show, Eq)

-- Annotated expression (expr + comments)
--data AnnExpr = AnnExpr
--  { expr :: Expr
--  , leading :: [Comment]
--  , trailing :: [Comment]
--  } deriving (Show, Eq)

lineComment :: Parser Comment
lineComment = do
    pos <- getPosition
    cmt <- manyTill anyChar lineEnding
    return $ Line (sourceLine pos) cmt

lineEnding :: Parser String
lineEnding = try (string "\r\n") <|> string "\n" <|> string "\r"

--blockComment :: Parser Comment
--blockComment = Block <$> (string "{-" *> manyTill anySingle (string "-}"))
--
--spaceWithComments :: Parser [Comment]
--spaceWithComments = many (lineComment <|> blockComment <|> (space1 *> pure []))

cmtParsed :: String -> [Comment]
cmtParsed input = case Text.Parsec.parse cmtParser "" input of
    Left err    -> error $ "Error while cut perse comments: " ++ show err
    Right right -> right
    -- concat $ map (\(Line l c) -> "Line " ++ show l ++ " " ++ (showPrettyString c)) right

    where
    cmtParser :: Parser [Comment]
    cmtParser = do
        res <- many $  (try cmtParserAfter) <|> (try cmtParserBefore) <|> noCmt
        return $ concat res

    noCmt :: Parser [Comment]
    noCmt = do
        a <- manyTill anyChar lineEnding
        return $ []

    cmtParserAfter :: Parser [Comment]
    cmtParserAfter = do
        anyUntil "==="
        spaces
        string "--"
        c <- lineComment
        return $ [c]

    cmtParserBefore :: Parser [Comment]
    cmtParserBefore = do
        anyUntil "--"
        c <- lineComment
        spaces
        string "==="
        return $ [c]

    anyUntil s = manyTill (noneOf "\n\r") (try (string s))

showPrettyString :: String -> String
showPrettyString = init . drop 1 . toUnicode . show
    where
    toUnicode :: String -> String
    toUnicode [] = []
    toUnicode ('\\':xs) = case numStr of
        [] -> '\\'  : toUnicode xs
        n  -> chr (read n) : toUnicode rest
        where
        (numStr, rest) = span (`elem` ['0'..'9']) xs
    toUnicode (x:xs) = x:toUnicode xs