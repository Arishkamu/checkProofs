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
goFunc bind = intercalate "\n\nEXPR=\n" $ map (goExpr 1) $ case bind of
    NonRec x ex -> [ex]
    Rec lex -> map snd lex


-- App:
--   |App:
--   |  |App:
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

goExpr :: Int -> CoreExpr -> String
goExpr ident expr = "\n" ++ replicate ident ' ' ++ case expr of
    (Var idx) -> "Var:" ++ show (ppr idx)
    (Lit lit) -> "Lit:" ++ show (ppr lit)
    (App ap ar) -> "App:" ++ goExpr (ident + 2) ap ++ goExpr (ident + 2) ar
    (Lam b lm) -> "Lam:" ++ show (ppr b) ++ goExpr (ident + 2) lm
    (Let _ ex) -> "Lam:" ++ goExpr (ident + 2) ex
    (Case ex _ _ _)  -> "Case:" ++ goExpr (ident + 2) ex ++ " Alt=NOT-IMPL"
    (Cast ex _) -> "Cast:" ++ goExpr (ident + 2) ex
    (Tick _ tex) -> "Tick:" ++ goExpr (ident + 2) tex
    (Type ty) -> "Type:" ++ show (ppr ty)
    (Coercion _) -> "Coercion"
