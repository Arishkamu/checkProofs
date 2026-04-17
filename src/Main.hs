{-# LANGUAGE LambdaCase, RecordWildCards#-}

import GHC
import GHC.Hs
import GHC.Types.SrcLoc
import GHC.Paths (libdir)
import GHC.Driver.Flags
import GHC.Utils.Outputable (Outputable, showSDocUnsafe, ppr)
import GHC.Core
import GHC.Data.Bag (Bag, bagToList)

import Control.Monad.IO.Class

import System.Directory (getCurrentDirectory)
import System.FilePath ((</>))

import Data.List (intercalate)
import Data.Generics.Uniplate.Data
import Data.Data

import Debug.Trace

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
    let tt = bagToList $ typecheckedSource typed
    liftIO $ putStrLn $ prettyPrint t
    liftIO $ putStrLn "\n\n=== ASTAST ===\n\n"
    let astInfo = collectAstInfo t
    liftIO $ putStrLn $ prettyPrint $ astInfo

    let findDiffInfo = astInfo
--    let p = pm_parsed_source parsed
--    liftIO $ putStrLn $ analyzeModule p
--    case tm_renamed_source typed of
--        Just r -> liftIO $ putStrLn $ analyzeModule p
--        Nothing -> liftIO $ putStrLn "Can't rename"
    liftIO $ putStrLn "THE END"

data Conversion = Conversion {
  lhs     :: HsExpr GhcTc,
  rhs     :: HsExpr GhcTc,
  comment :: String,        -- Maybe HsExpr GhcPs to substitute
  lDiff   :: HsExpr GhcTc,
  rDiff   :: HsExpr GhcTc
}

-- Add local Where to DeclConversions???
type DeclConversions = (LIdP GhcTc, [Conversion])

data AstInfo = AstInfo {
  declConvrs  :: [DeclConversions], -- List of Conversion per decl
  funcDefs    :: [HsBindLR GhcTc GhcTc]
}

instance Semigroup AstInfo where
  AstInfo c1 f1 <> AstInfo c2 f2 = AstInfo (c1 <> c2) (f1 <> f2)

instance Monoid AstInfo where
  mempty = AstInfo [] []



class PrettyPrint a where
  prettyPrint :: a -> String

prettyPrintStrs :: [String] -> String
prettyPrintStrs = intercalate "\n  "

instance (PrettyPrint a) => PrettyPrint (GenLocated SrcSpanAnnA a) where
  prettyPrint (L _ x) = prettyPrint x

instance PrettyPrint (Id) where
  prettyPrint x = "ID: " ++ showSDocUnsafe (ppr x)

instance PrettyPrint (GenLocated SrcSpanAnnN Id) where
  prettyPrint (L _ x) = prettyPrint x

instance PrettyPrint Conversion where
  prettyPrint Conversion{..} = comment ++ " :: " ++ showSDocUnsafe (ppr lhs) ++ " => " ++ showSDocUnsafe (ppr rhs) ++
    "\n    Different constructors: " ++ show (toConstr lDiff) ++ " vs " ++ show (toConstr rDiff) ++
    "\n      l: " ++ prettyPrint lDiff ++ "\n      r: " ++ prettyPrint rDiff

instance PrettyPrint AstInfo where
  prettyPrint AstInfo{..} =
    "===== AstInfo =====" ++
    "\nDeclConvrs:" ++ prettyPrintStrs (concatMap makePretty declConvrs)  ++
    "\nFunDefs:" ++ prettyPrint funcDefs

    where
    makePretty (decl, convrs) = (("\n  DeclName: " ++  prettyPrint decl) : map (\cnv -> "  " ++ prettyPrint cnv) convrs)

-- Represent: LHsBindLR GhcTc
--instance PrettyPrint (HsBindLR GhcTc GhcTc) where
--  prettyPrint (L _ bind) = prettyPrint bind

instance PrettyPrint (HsBindLR GhcTc GhcTc) where
  prettyPrint bind =
--  show (toConstr bind) ++ " :: " ++ (showSDocUnsafe (ppr bind))
    case bind of
      fb@FunBind{ fun_matches = mg } -> "FUNBIND: " ++ "\nID:" ++ showSDocUnsafe (ppr (unLoc (fun_id fb))) ++ "\n" ++ (showSDocUnsafe (ppr bind))
--      analyzeMatchGroup mg
--          PatBind{} -> []
--          VarBind{} ->
--          PatSynBind{} -> "PatSynBind"
      (XHsBindsLR a) -> "XHsBindsLR" ++ " :: " ++ prettyPrint (abs_binds a)
      _ -> show (toConstr bind) ++ " :: " ++ (showSDocUnsafe (ppr bind))

instance PrettyPrint (HsExpr GhcTc) where
  prettyPrint expr = show (toConstr expr) ++ " :: " ++ (showSDocUnsafe (ppr expr))

instance (PrettyPrint a, PrettyPrint b) => PrettyPrint (a, b) where
  prettyPrint (x, y) = "(\n  " ++ prettyPrint x ++ "\n  " ++ prettyPrint y ++ "\n)"

instance (PrettyPrint a) => PrettyPrint [a] where
  prettyPrint as = intercalate "\n  " $ map prettyPrint as

instance (PrettyPrint a) => PrettyPrint (Bag a) where
  prettyPrint = prettyPrint . bagToList



collectAstInfo :: TypecheckedSource -> AstInfo
collectAstInfo binds = mconcat $ map collectBind (bagToList binds)

collectBind :: LHsBind GhcTc -> AstInfo
collectBind (L _ bind) = case bind of
  FunBind{..} -> AstInfo (collectMatchGroup fun_id fun_matches) [bind]
  XHsBindsLR a -> mconcat $ map collectBind $ bagToList (abs_binds a)
  _ -> mempty
--    PatBind{} -> []
--    VarBind{} -> []
--    PatSynBind{} -> "PatSynBind"

collectMatchGroup :: LIdP GhcTc -> MatchGroup GhcTc (LHsExpr GhcTc) -> [DeclConversions]
collectMatchGroup funId mg = map (analyzeMatch . unLoc) matches where
  matches = unLoc (mg_alts mg)
  analyzeMatch Match{..} = {- get List of Pats, construct id-}
    (funId, concatMap analyzeGRHS (grhssGRHSs m_grhss) ) {- ignore local -}
  analyzeGRHS (L _ (GRHS _ _ body)) = collectExpr body

collectExpr :: LHsExpr GhcTc -> [Conversion]
collectExpr (L _ expr) = map getConvrs pairs where
--  aaa = intercalate "\n" $ map (\(a1, a2) -> show (toConstr a1) ++ " :: " ++ showSDocUnsafe (ppr a1) ++ "\n  " ++ show (toConstr a2) ++ " :: " ++ showSDocUnsafe (ppr a2)) [(e, ae) | e@(HsApp _ (L _ (HsApp _ (L _ ae) argExpr)) argComm) <- universe expr]
  argWithInfo = [(argExpr, argComm) |
    (HsApp _ (L _ (HsApp _ (L _ exprName) argExpr)) argComm) <- universe expr,
    "WithInfo" <- [showSDocUnsafe (ppr exprName)] ]
--    argWithInfo = map (\(f, s, t) -> (f, s)) $ filter (\(_, _, name) -> (showSDocUnsafe (ppr name)) == "WithInfo") argName
  pairs  = zip argWithInfo (drop 1 argWithInfo)
--  getConvrs :: (GenLocated SrcSpanAnnA (HsExpr GhcTc), GenLocated SrcSpanAnnA (HsExpr GhcTc)) -> (GenLocated SrcSpanAnnA (HsExpr GhcTc), GenLocated SrcSpanAnnA (HsExpr GhcTc)) -> Conversion
  getConvrs ((L _ lhe, c1), (L _ rhe, _)) = getConvrsWithDiff lhe rhe (toStr c1) (findDiff lhe rhe)
  getConvrsWithDiff lhe rhe comm (diffL, diffR) = Conversion lhe rhe comm diffL diffR
  toStr (L _ (HsLit _ lit)) = showSDocUnsafe (ppr lit)


findDiff :: HsExpr GhcTc -> HsExpr GhcTc -> (HsExpr GhcTc, HsExpr GhcTc)
findDiff x y = firstDiffList (universe x) (universe y)
  where
  firstDiffList :: [HsExpr GhcTc] -> [HsExpr GhcTc] -> (HsExpr GhcTc, HsExpr GhcTc)
  firstDiffList (x:xs) (y:ys)
    | toConstr x /= toConstr y && (show (toConstr x) == "HsPar") =
      firstDiffList xs (y:ys)
    | toConstr x /= toConstr y && (show (toConstr y) == "HsPar") =
      firstDiffList (x:xs) ys
    | toConstr x /= toConstr y = (x, y)
    | otherwise =
      firstDiffList xs ys


{-
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

-}

