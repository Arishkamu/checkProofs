{-# LANGUAGE LambdaCase #-}

import GHC
import GHC.Paths (libdir)
import GHC.Driver.Flags
import GHC.Utils.Outputable
import GHC.Core

import Control.Monad.IO.Class

import System.Directory (getCurrentDirectory)
import System.FilePath ((</>))

import Data.List (intercalate)
import Data.Generics.Uniplate.Data
import Data.Data

main :: IO ()
main =
  runGhc (Just libdir) $ do
    dflags <- getSessionDynFlags
    _ <- setSessionDynFlags dflags

    -- load the file
--    let path = "/Users/arina/hse/nir/moskvinPrj/checkProofs/test/BasicTest.hs"
    let path = "/Users/arina/hse/nir/moskvinPrj/checkProofs/old/Example.hs"

    core <- compileToCoreModule path

    liftIO $ putStrLn "=== Core AST ==="
    liftIO $ putStrLn (showSDocUnsafe (ppr $ cm_binds core))

    let bindGlExprs = map goFunc (cm_binds core)
    liftIO $ putStrLn $ intercalate "\n" bindGlExprs
--    mapM_ (\ex -> liftIO (putStrLn ("=======\n" ++ (showSDocUnsafe (ppr ex))))) bindGlExprs

--    case mgModSummaries modGraph of
--      [] -> liftIO $ putStrLn "No module found"
--      (ms:_) -> do
--        p <- parseModule ms
--        let parsed = pm_parsed_source p
--        liftIO $ putStrLn $ analyzeModule parsed
--        liftIO $ putStrLn (showSDocUnsafe (ppr parsed))


--goFunc :: CoreBind -> [CoreExpr]
--goFunc bind = flatmap goExpr $ case bind of
--    NonRec x ex -> [ex]
--    Rec lex -> map snd lex

goFunc :: CoreBind -> String
goFunc bind = intercalate "\n\nEXPR=\n" $ map (goExpr) $ case bind of
    NonRec x ex -> [ex]
    Rec lex -> map snd lex


-- App1:
--   |App2:
--   |  |App3:
--   |  |  |Var:WithInfo
--   |  |  |Type:a_aBd -> d_aBb
--   |  |App:
--   |  |  |App:
--   |  |  |  App:
--   |  |  |    App:
--   |  |  |      App:
--   |  |  |        Var:.
--   |  |  |        Type:c_aBa
--   |  |  |      Type:d_aBb
--   |  |  |    Type:a_aBd
--   |  |  |  Var:f_agN
--   |  |  |App:
--   |  |  |  App:
--   |  |  |    App:
--   |  |  |      App:
--   |  |  |        App:
--   |  |  |          Var:.
--   |  |  |          Type:b_aBc
--   |  |  |        Type:c_aBa
--   |  |  |      Type:a_aBd
--   |  |  |    Var:g_agO
--   |  |  |  Var:h_agP
--   |App:
--   |  |Var:unpackCString#
--   |  |Lit:"(.)"#

printExpr :: Int -> CoreExpr -> String
printExpr ident expr = "\n" ++ replicate ident ' ' ++ case expr of
    (Var idx) -> "Var:" ++ show (ppr idx)
    (Lit lit) -> "Lit:" ++ show (ppr lit)
    (App ap ar) -> "App:" ++ printExpr (ident + 2) ap ++ printExpr (ident + 2) ar
    (Lam b lm) -> "Lam:" ++ show (ppr b) ++ printExpr (ident + 2) lm
    (Let _ ex) -> "Lam:" ++ printExpr (ident + 2) ex
    (Case ex _ _ _)  -> "Case:" ++ printExpr (ident + 2) ex ++ " Alt=NOT-IMPL"
    (Cast ex _) -> "Cast:" ++ printExpr (ident + 2) ex
    (Tick _ tex) -> "Tick:" ++ printExpr (ident + 2) tex
    (Type ty) -> "Type:" ++ show (ppr ty)
    (Coercion _) -> "Coercion"

goExpr :: CoreExpr -> String
goExpr expr = "\nAAAA: " ++ intercalate "\n" (toStrLsEquat) where
    argName = [(argExpr, argComm, name) | (App (App (App (Var name) _) argExpr) argComm) <- universe expr]
    argAppl = map (\(f, s, t) -> (f, s)) $ filter (\(_, _, name) -> (show (ppr name)) == "WithInfo") argName
    pairs = map (\((x1, c1), (x2, c2)) -> (x1, x2, toStr c1)) (zip argAppl (drop 1 argAppl))
    toStr (App _ (Lit lit)) = show (ppr lit)
----    firstDiff = map findDiff pairs
    toStrLsEquat = "EQUAT:" : map (\(x, y, z) -> (show (ppr x)) ++ ", " ++ (show (ppr y)) ++ " :: " ++ z) pairs
----    toStrLsDiff  = map (\x -> "DIFF: " ++ (showSDocUnsafe (ppr x))) firstDiff
----    toStrLsDiff  = map (\x -> "DIFF: " ++ x) firstDiff
----    toStrLs = map (\(x, y) -> "EQUAT: " ++ (showSDocUnsafe (ppr x)) ++ ", " ++ (showSDocUnsafe (ppr y))) argAppl


--    AAAA: EQUAT:
--    . @c_aBa @d_aBb @a_aBd f_agN (. @b_aBc @c_aBa @a_aBd g_agO h_agP),
--            \ (x_agQ :: a_aBd) -> f_agN (. @b_aBc @c_aBa @a_aBd g_agO h_agP x_agQ)
--            :: "(.)"#
--    \ (x_agQ :: a_aBd) -> f_agN (. @b_aBc @c_aBa @a_aBd g_agO h_agP x_agQ),
--            \ (x_agR :: a_aBd) -> f_agN (g_agO (h_agP x_agR))
--            :: "(.)"#
--    \ (x_agR :: a_aBd) -> f_agN (g_agO (h_agP x_agR)),
--        \ (x_agT :: a_aBd) -> f_agN (g_agO (h_agP x_agT))
--        :: "{beta}"#
--    \ (x_agT :: a_aBd) -> f_agN (g_agO (h_agP x_agT)),
--        \ (x_agU :: a_aBd) -> f_agN (g_agO (h_agP x_agU))
--        :: "{beta \\208\\191\\209\\128\\208\\184\\208\\178\\208\\181\\209\\130}"#
--    \ (x_agU :: a_aBd) -> f_agN (g_agO (h_agP x_agU)),
--        \ (x_agW :: a_aBd) -> . @c_aBa @d_aBb @b_aBc f_agN g_agO (h_agP x_agW)
--        :: "(.)"#
--    \ (x_agW :: a_aBd) -> . @c_aBa @d_aBb @b_aBc f_agN g_agO (h_agP x_agW),
--        . @b_aBc @d_aBb @a_aBd (. @c_aBa @d_aBb @b_aBc f_agN g_agO) h_agP
--        :: "(.)"#