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
    target <- guessTarget path Nothing Nothing
    setTargets [target]

    -- parse it
    modGraph <- depanal [] False
    let ms = head $ mgModSummaries modGraph
--
--    parsed <- parseModule ms
--
--    liftIO $ putStrLn "=== Parsed AST ==="
--    liftIO $ putStrLn (showSDocUnsafe (ppr (pm_parsed_source parsed)))
--
--    typed <- typecheckModule parsed
--
--    liftIO $ putStrLn "=== Renamed AST ==="
--    liftIO $ putStrLn (showSDocUnsafe (ppr (tm_renamed_source typed)))
--
--    liftIO $ putStrLn "=== Typechecked AST ==="
--    liftIO $ putStrLn (showSDocUnsafe (ppr (tm_typechecked_source typed)))
--
--    desugared <- desugarModule typed
--
--    core <- compileToCoreModule path
--
--    liftIO $ putStrLn "=== Core AST ==="
--    liftIO $ putStrLn (showSDocUnsafe (ppr $ cm_binds core))
--
--    let bindGlExprs = map goFunc (cm_binds core)
--    liftIO $ putStrLn $ intercalate "\n" bindGlExprs
--    mapM_ (\ex -> liftIO (putStrLn ("=======\n" ++ (showSDocUnsafe (ppr ex))))) bindGlExprs

    case mgModSummaries modGraph of
      [] -> liftIO $ putStrLn "No module found"
      (ms:_) -> do
        p <- parseModule ms
        let parsed = pm_parsed_source p
        liftIO $ putStrLn $ analyzeModule parsed
        liftIO $ putStrLn (showSDocUnsafe (ppr parsed))



--analyzeModule :: ParsedSource -> String
--analyzeModule (L _ modu) =
--  case hsmodDecls modu of
--    decls -> concatMap analyzeDecl decls

analyzeModule :: ParsedSource -> String
analyzeModule (L _ modu) =
  case hsmodDecls modu of
    decls -> concatMap analyzeDecl decls

analyzeDecl :: LHsDecl GhcPs -> String
analyzeDecl (L _ decl) =
  case decl of
    ValD _ bind -> analyzeBind bind
    TyClD _ t   -> "Type\n"
    _           -> "AnyDecl\n"

--analyzeBind :: HsBind GhcPs -> String
--analyzeBind bind =
--  case bind of
--    FunBind _ _ _ -> "FunBind\n"
--    _           -> "AnyBind\n"
analyzeBind :: HsBind GhcPs -> String
analyzeBind bind =
  case bind of
    FunBind { fun_matches = mg } -> analyzeMatchGroup mg
    PatBind {} -> "Pattern binding"
    _ -> "AnyBind"

analyzeMatchGroup :: MatchGroup GhcPs (LHsExpr GhcPs) -> String
analyzeMatchGroup mg = concatMap analyzeMatch (unLoc (mg_alts mg))

analyzeMatch :: LMatch GhcPs (LHsExpr GhcPs) -> String
analyzeMatch (L _ match) = analyzeGRHSs (m_grhss match)

analyzeGRHSs :: GRHSs GhcPs (LHsExpr GhcPs) -> String
analyzeGRHSs grhss = concatMap analyzeGRHS (grhssGRHSs grhss)

analyzeGRHS :: LGRHS GhcPs (LHsExpr GhcPs) -> String
analyzeGRHS (L _ (GRHS _ _ body)) = analyzeExpr body

analyzeExpr :: LHsExpr GhcPs -> String
analyzeExpr (L _ expr) =
    case expr of
        OpApp _ l op r -> "Operator application: {\n" ++ "OP  " ++ analyzeExpr op ++ "\n  " ++ analyzeExpr l ++ "\n  " ++ analyzeExpr r ++ "}\n"
        _ -> (showSDocUnsafe (ppr expr))
--  case expr of
--    HsApp _ f arg -> "Application: {\n" ++ analyzeExpr f ++ "\n" ++ analyzeExpr arg ++ "}\n"
--    OpApp _ l op r -> "Operator application: {\n" ++ analyzeExpr l ++ "\n" ++ analyzeExpr r ++ "}\n"
--    HsLam _ _ mg -> "Lambda: {\n" ++ analyzeMatchGroup mg  ++ "}\n"
--    HsLet _ _ body -> analyzeExpr body
--    HsIf _ a b c -> analyzeExpr a ++ analyzeExpr b ++ analyzeExpr c
--    HsVar _ name -> "Var: " ++ (showSDocUnsafe (ppr name))
--    HsLit _ lit -> "Literal: " ++ (showSDocUnsafe (ppr lit))
--    _ -> "AnyExpr\n"

