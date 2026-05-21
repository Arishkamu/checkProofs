{-|
Module      : Main
Description : Analuzing equational reasoning
License     : MIT
-}
module Main where

import CheckProofs
import System.Environment (getArgs)
import System.FilePath ((</>))


filePathDefault :: FilePath
filePathDefault = "examples" </> "AllGoodExamples.hs"

main :: IO ()
main = do
  sys_args <- getArgs
  let filePath = case sys_args of
        [path] -> path
        []     -> filePathDefault
        _      -> error $ "Extra arguments. Please provide only analyzing file path \nor nothing if you want to use default one: `" ++ filePathDefault ++ "`"
  checkProofs filePath
