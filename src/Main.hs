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
analyzeExpr (L _ expr) = intercalate "\n" (toStrLsEquat ++ toStrLsDiff) where
    argName = [(argExpr, argComm, name) | (HsApp _ (L _ (HsApp _ (L _ (HsVar _ name)) argExpr)) argComm) <- universe expr]
    argAppl = map (\(f, s, t) -> (f, s)) $ filter (\(_, _, name) -> (showSDocUnsafe (ppr name)) == "WithInfo") argName
    pairs = map (\((x1, c1), (x2, c2)) -> (unLoc x1, unLoc x2, toStr c1)) (zip argAppl (drop 1 argAppl))
    toStr (L _ (HsLit _ lit)) = (showSDocUnsafe (ppr lit))
    firstDiff = map findDiff pairs
    toStrLsEquat = "EQUAT:" : map (\(x, y, z) -> (showSDocUnsafe (ppr x)) ++ ", " ++ (showSDocUnsafe (ppr y)) ++ " :: " ++ z) pairs
--    toStrLsDiff  = map (\x -> "DIFF: " ++ (showSDocUnsafe (ppr x))) firstDiff
    toStrLsDiff  = map (\x -> "DIFF: " ++ x) firstDiff
--    toStrLs = map (\(x, y) -> "EQUAT: " ++ (showSDocUnsafe (ppr x)) ++ ", " ++ (showSDocUnsafe (ppr y))) argAppl


findDiff :: (HsExpr GhcPs, HsExpr GhcPs, String) -> String
findDiff (x, y, comm) = firstDiffList (universe x) (universe y)

firstDiffList :: [HsExpr GhcPs] -> [HsExpr GhcPs] -> String
firstDiffList [] [] = "Nothing"
firstDiffList (x:xs) (y:ys)
  | toConstr x /= toConstr y && (show (toConstr x) == "HsPar") =
    firstDiffList xs (y:ys)
  | toConstr x /= toConstr y && (show (toConstr y) == "HsPar") =
    firstDiffList (x:xs) ys
  | toConstr x /= toConstr y =
    "Different constructors: " ++ show (toConstr x) ++ " vs " ++ show (toConstr y) ++ "\nl: " ++ printExpr x ++ "r: " ++ printExpr y
  | otherwise =
    firstDiffList xs ys
firstDiffList _ _ = "Different number of children"


printLExpr :: LHsExpr GhcPs -> String
printLExpr = printExpr . unLoc

printExpr :: HsExpr GhcPs -> String
printExpr expr =
  case expr of
    HsApp _ f arg -> "Application: {\n" ++ printLExpr f ++ "\n" ++ printLExpr arg ++ "}\n"
    OpApp _ l op r -> "Operator application: {\n" ++ printLExpr l ++ "\n" ++ printLExpr r ++ "}\n"
    HsLam _ mg -> "Lambda: {\n" ++ "matchGroup" ++ "}\n"
    HsLet _ _ _ _ body -> printLExpr body
    HsIf _ a b c -> printLExpr a ++ printLExpr b ++ printLExpr c
    HsVar _ name -> "Var: " ++ (showSDocUnsafe (ppr name))
    HsLit _ lit -> "Literal: " ++ (showSDocUnsafe (ppr lit))
    HsPar _ _ exp _ -> printLExpr exp
    _ -> "AnyExpr\n"

