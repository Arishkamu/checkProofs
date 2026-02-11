{-# LANGUAGE TemplateHaskell #-}
module Main where

--import Language.Haskell.Exts.Parser
--import Language.Haskell.Exts.ExactPrint
--import Language.Haskell.Exts.Syntax
--import Language.Haskell.Exts.SrcLoc
--import Language.Haskell.Exts.Pretty
--import Language.Haskell.Exts.Comments
--import Language.Haskell.Exts

import Language.Haskell.TH.Syntax

import System.Directory (getCurrentDirectory)
import System.FilePath ((</>))

import CommentParser (cmtParsed)
import Extra


-- $(myAST)

main :: IO ()
main = do
    dir <- getCurrentDirectory
    src <- readFile $ dir </> "test" </> "BasicTest.hs"
    putStrLn $ cmtParsed src
    expr1 <- runQ $ myAST1
    print $ expr1
    expr2 <- runQ $ myAST2
    print $ expr2
--    let code1 = "f . (g . h)"
--    let code2 = "\\x -> f ((g . h) x)"
--    putStrLn "================="
--    case parseExp code1 of
--        ParseOk ast -> print ast
--        ParseFailed loc msg -> putStrLn $ "Parse error at " ++ show loc ++ ": " ++ msg
--    putStrLn "====="
--    case parseExp code2 of
--        ParseOk ast -> print ast
--        ParseFailed loc msg -> putStrLn $ "Parse error at " ++ show loc ++ ": " ++ msg