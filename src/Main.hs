{-# LANGUAGE LambdaCase, RecordWildCards#-}

import GHC
import GHC.Hs
import GHC.Types.SrcLoc
import GHC.Paths (libdir)
import GHC.Driver.Flags
import GHC.Utils.Outputable (Outputable, showSDocUnsafe, ppr)
import GHC.Core
import GHC.Data.Bag (Bag, bagToList)

import Language.Haskell.Syntax

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

    let path = "/Users/arina/hse/nir/moskvinPrj/checkProofs/old/Example.hs"
    target <- guessTarget path Nothing Nothing
    setTargets [target]
    load LoadAllTargets

    modGraph <- depanal [] False
    let ms = head $ mgModSummaries modGraph

    let ms = head $ mgModSummaries modGraph

    parsed <- parseModule ms

--    liftIO $ putStrLn "\n=== Parsed AST ==="
--    liftIO $ putStrLn (showSDocUnsafe (ppr (pm_parsed_source parsed)))
--
    typed <- typecheckModule parsed
--
--    liftIO $ putStrLn "\n=== Renamed AST ==="
--    liftIO $ putStrLn (showSDocUnsafe (ppr (tm_renamed_source typed)))
--
    liftIO $ putStrLn "\n=== Typechecked AST ==="
    liftIO $ putStrLn (showSDocUnsafe (ppr (tm_typechecked_source typed)))
    liftIO $ putStrLn "\n=== AST ==="

--    case mgModSummaries modGraph of
--      [] -> liftIO $ putStrLn "No module found"
--      (ms:_) -> do
--        p <- parseModule ms
    let t = typecheckedSource typed
    let t = bagToList $ typecheckedSource typed
    liftIO $ putStrLn $ prettyPrint t
--    let p = pm_parsed_source parsed
--    liftIO $ putStrLn $ analyzeModule p
--    case tm_renamed_source typed of
--        Just r -> liftIO $ putStrLn $ analyzeModule p
--        Nothing -> liftIO $ putStrLn "Can't rename"
    liftIO $ putStrLn "THE END"

data Conversion = Conversion {
  lhs     :: HsExpr GhcTc,
  rhs     :: HsExpr GhcTc,
  comment :: String        -- Maybe HsExpr GhcPs to substitute
}

type DeclConversions = (HsDecl GhcTc, [Conversion])

data AstInfo = AstInfo {
  declConvrs  :: [DeclConversions], -- List of Conversion per decl
  funcDefs    :: [String]
}

instance Semigroup AstInfo where
  AstInfo c1 f1 <> AstInfo c2 f2 = AstInfo (c1 <> c2) (f1 <> f2)

instance Monoid AstInfo where
  mempty = AstInfo [] []



class PrettyPrint a where
  prettyPrint :: a -> String

prettyPrintStrs :: [String] -> String
prettyPrintStrs = intercalate "\n  "

instance PrettyPrint Conversion where
  prettyPrint Conversion{..} = comment ++ " :: " ++ showSDocUnsafe (ppr lhs) ++ " => " ++ showSDocUnsafe (ppr rhs)

instance PrettyPrint AstInfo where
  prettyPrint AstInfo{..} =
    "===== AstInfo =====" ++
    "\nDeclConvrs:" ++ prettyPrintStrs (concatMap makePretty declConvrs)  ++
    "\nFunDefs:" ++ prettyPrintStrs funcDefs

    where
    makePretty (decl, convrs) = "DeclName:" : map (\cnv -> "  " ++ prettyPrint cnv) convrs

-- Represent: LHsBindLR GhcTc
instance PrettyPrint (GenLocated SrcSpanAnnA (HsBindLR GhcTc GhcTc)) where
  prettyPrint (L _ bind) =
    case bind of
--        FunBind{ fun_matches = mg } -> "FUNBIND: " ++ (showSDocUnsafe (ppr bind)) ++ "\n" ++ analyzeMatchGroup mg
--        PatBind{} -> []
--        VarBind{} ->
--        PatSynBind{} -> "PatSynBind"
--      (XHsBindsLR a) -> "XHsBindsLR" ++ " :: " ++ prettyPrint (abs_binds a)
      _ -> show (toConstr bind) ++ " :: " ++ (showSDocUnsafe (ppr bind))

instance (PrettyPrint a) => PrettyPrint [a] where
  prettyPrint as = intercalate "\n  " $ map prettyPrint as

instance (PrettyPrint a) => PrettyPrint (Bag a) where
  prettyPrint = prettyPrint . bagToList



collectAstInfo :: TypecheckedSource -> AstInfo
collectAstInfo binds = mconcat $ map collectBinds (bagToList binds)

collectBind :: LHsBind GhcPs -> AstInfo
collectBind (L _ bind) = AstInfo  funDefs

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
    FunBind { fun_matches = mg } -> "FUNBIND: " ++ (showSDocUnsafe (ppr bind)) ++ "\n" ++ analyzeMatchGroup mg
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
findDiff (x, y, comm) = "Different constructors: " ++ show (toConstr xd) ++ " vs " ++ show (toConstr yd) ++ "\nl: " ++ printExpr xd ++ "r: " ++ printExpr yd
    where
    (xd, yd) = firstDiffList (universe x) (universe y)

firstDiffList :: [HsExpr GhcPs] -> [HsExpr GhcPs] -> (HsExpr GhcPs, HsExpr GhcPs)
firstDiffList (x:xs) (y:ys)
  | toConstr x /= toConstr y && (show (toConstr x) == "HsPar") =
    firstDiffList xs (y:ys)
  | toConstr x /= toConstr y && (show (toConstr y) == "HsPar") =
    firstDiffList (x:xs) ys
  | toConstr x /= toConstr y = (x, y)
  | otherwise =
    firstDiffList xs ys


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

