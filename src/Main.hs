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

    let ms = head $ mgModSummaries modGraph

    parsed <- parseModule ms

    liftIO $ putStrLn "\n=== Parsed AST ==="
    liftIO $ putStrLn (showSDocUnsafe (ppr (pm_parsed_source parsed)))

    typed <- typecheckModule parsed

    liftIO $ putStrLn "\n=== Renamed AST ==="
    liftIO $ putStrLn (showSDocUnsafe (ppr (tm_renamed_source typed)))

    liftIO $ putStrLn "\n=== Typechecked AST ==="
    liftIO $ putStrLn (showSDocUnsafe (ppr (tm_typechecked_source typed)))
    liftIO $ putStrLn "\n=== AST ==="

--    case mgModSummaries modGraph of
--      [] -> liftIO $ putStrLn "No module found"
--      (ms:_) -> do
--        p <- parseModule ms
    let p = pm_parsed_source parsed
    liftIO $ putStrLn $ analyzeModule p
--    case tm_renamed_source typed of
--        Just r -> liftIO $ putStrLn $ analyzeModule p
--        Nothing -> liftIO $ putStrLn "Can't rename"


analyzeModule :: ParsedSource -> String
analyzeModule (L _ modu) =
  case hsmodDecls modu of
    decls -> concatMap analyzeDecl decls

analyzeDecl :: LHsDecl GhcPs -> String
analyzeDecl (L _ decl) =
  case decl of
    ValD _ bind -> analyzeBind bind
    TyClD _ t   -> []
    _           -> []

analyzeBind :: HsBind GhcPs -> String
analyzeBind bind =
  case bind of
    FunBind { fun_matches = mg } -> analyzeMatchGroup mg
    PatBind {} -> []
    _ -> []

analyzeMatchGroup :: MatchGroup GhcPs (LHsExpr GhcPs) -> String
analyzeMatchGroup mg = concatMap analyzeMatch (unLoc (mg_alts mg))

analyzeMatch :: LMatch GhcPs (LHsExpr GhcPs) -> String
analyzeMatch (L _ match) = analyzeGRHSs (m_grhss match)

analyzeGRHSs :: GRHSs GhcPs (LHsExpr GhcPs) -> String
analyzeGRHSs grhss = concatMap analyzeGRHS (grhssGRHSs grhss)

analyzeGRHS :: LGRHS GhcPs (LHsExpr GhcPs) -> String
analyzeGRHS (L _ (GRHS _ _ body)) = analyzeExpr body

analyzeExpr :: LHsExpr GhcPs -> String
analyzeExpr (L _ expr) = intercalate "\n" toStrLs where
    argName = [(argExpr, argComm, name) | (HsApp _ (L _ (HsApp _ (L _ (HsVar _ name)) argExpr)) argComm) <- universe expr]
    argAppl = map (\(f, s, t) -> (f, s)) $ filter (\(_, _, name) -> (showSDocUnsafe (ppr name)) == "WithInfo") argName
    p1 = (drop 1 argAppl)
    p2 = zip argAppl p1
    pairs = map (\((x1, c1), (x2, c2)) -> (x1, x2, toStr c1)) p2
    toStr (L _ (HsLit _ lit)) = (showSDocUnsafe (ppr lit))
--    firstDiff = map findDiff pairs
    toStrLs = map (\(x, y, z) -> "EQUAT: " ++ (showSDocUnsafe (ppr x)) ++ ", " ++ (showSDocUnsafe (ppr y)) ++ " :: " ++ z) pairs
--    toStrLs = map (\x -> "DIFF: " ++ (showSDocUnsafe (ppr x))) firstDiff
--    toStrLs = map (\(x, y) -> "EQUAT: " ++ (showSDocUnsafe (ppr x)) ++ ", " ++ (showSDocUnsafe (ppr y))) argAppl
--    case expr of
--        OpApp _ l op r
--            | (showSDocUnsafe (ppr op)) == "(====)" -> "{\n  lll" ++ "\n  r:" ++ (showSDocUnsafe (ppr r)) ++ "}\n" ++ analyzeExpr l ++ analyzeExpr r
--            | otherwise -> analyzeExpr l ++ analyzeExpr r
--        HsApp _ f arg -> analyzeExpr f ++ analyzeExpr arg
--        HsPar _ _ exp _ -> analyzeExpr exp
--        _ -> "Other"
--  case expr of
--    HsApp _ f arg -> "Application: {\n" ++ analyzeExpr f ++ "\n" ++ analyzeExpr arg ++ "}\n"
--    OpApp _ l op r -> "Operator application: {\n" ++ analyzeExpr l ++ "\n" ++ analyzeExpr r ++ "}\n"
--    HsLam _ mg -> "Lambda: {\n" ++ analyzeMatchGroup mg  ++ "}\n"
--    HsLet _ _ _ _ body -> analyzeExpr body
--    HsIf _ a b c -> analyzeExpr a ++ analyzeExpr b ++ analyzeExpr c
--    HsVar _ name -> "Var: " ++ (showSDocUnsafe (ppr name))
--    HsLit _ lit -> "Literal: " ++ (showSDocUnsafe (ppr lit))
--    HsGetField _ fild fl_name -> "GetField: " ++ (showSDocUnsafe (ppr fl_name)) ++ "\n: " ++ analyzeExpr fild
--    HsPar _ _ exp _ -> analyzeExpr exp
--    _ -> "AnyExpr: " ++ (showSDocUnsafe (ppr expr)) ++ "\n"


--firstDiff :: (HsExpr GhcPs, HsExpr GhcPs, String) ->