module Main where

import System.Directory (getCurrentDirectory)
import System.FilePath ((</>))

import CommentParser (cmtParsed)

main :: IO ()
main = do
    dir <- getCurrentDirectory
    src <- readFile $ dir </> "test" </> "BasicTest.hs"
    putStrLn $ show $ cmtParsed src